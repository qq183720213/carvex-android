package io.github.iamr0s.carvex.session
import io.github.iamr0s.carvex.carplay.*
import io.github.iamr0s.carvex.sessioncore.*

import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothManager
import android.content.Context
import android.os.SystemClock
import android.view.*
import java.nio.ByteBuffer
import java.nio.ByteOrder
import kotlin.math.PI
import kotlin.math.sin
import io.github.iamr0s.carvex.carplay.core.*
import io.github.iamr0s.carvex.pcm.*
import io.github.iamr0s.carvex.protocol.api.ProtocolStack
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.sync.Mutex
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.*

/** Splash duration before the host takes the encoder surface. */
private const val SPLASH_MILLIS=6_000L

private const val MIN_BITRATE=1_000_000

/** 按像素率估算码率：约 0.13 bit/像素/帧，最低 1 Mbps。
 *  例：1080p30≈8.1 Mbps、720p30≈3.6 Mbps、1080p60≈16.2 Mbps。 */
private fun nominalBitrate(width:Int,height:Int,fps:Int):Int {
    val pixelFramesPerSecond=width.toLong()*height*fps
    return (pixelFramesPerSecond*13/100).toInt().coerceAtLeast(MIN_BITRATE)
}

class SessionController(
    private val context:Context,
    private val localContent:LocalVideoContentFactory?=null,
    /** 由 `:app` 注入的宿主编排工厂；编排层不再认识任何具体宿主模块。 */
    private val hostFactory:(Context,HostCallbacks)->CastHost,
    /** 由 `:app` 注入的协议栈；编排层只按它声明的能力决策，不认识具体协议实现。 */
    private val protocol:ProtocolStack) : CastSession {
    private val scope=CoroutineScope(SupervisorJob()+Dispatchers.Main.immediate)
    private var job:Job?=null
    @Volatile private var termination:SessionTermination?=null
    @Volatile private var host:CastHost?=null
    @Volatile private var audioBridge:HostAudioBridge?=null
    @Volatile private var activeAir:AirSession?=null
    @Volatile private var micQueryLogged=false
    /** Wi-Fi parameters from the last successful handshake: a retry reuses them instead of asking the
     *  accessory again, and a re-handshake can tell from them that nothing changed. */
    @Volatile private var lastBootstrap:WifiBootstrap?=null
    private var carPlayAudioTestJob:Job?=null
    private var carWithAudioProbeJob:Job?=null
    private data class AudioProbeSample(val category:Int,val rate:Int,val channels:Int,val bytes:Int,val nonzero:Boolean)
    private val audioProbeSamples=Channel<AudioProbeSample>(64)
    /** Only while the CarWith audio probe is listening: the host PCM callback runs for every block. */
    @Volatile private var audioProbeListening=false
    @Volatile private var applyDynamicFps:((Int)->Unit)?=null
    @Volatile private var applyBitrate:((Int)->Unit)?=null
    /** 当前会话里"把一个 CarWith 键码按下/松开发给宿主"的入口；CarPlay 事件映射与手动模拟共用。 */
    @Volatile private var sendKey:((Int,Boolean)->Boolean)?=null
    private val timer=Executors.newSingleThreadScheduledExecutor{r->Thread(r,"session-deadline").apply{isDaemon=true}}
    @Volatile private var disconnecting=false
    override val active:Boolean get()=disconnecting||job?.isActive==true
    override fun start(fromHost:Boolean) {
        if(active)return
        val options=BridgeStore.options.value
        if(!options.experiment){reject("首次使用请在设置中了解并启用实验认证模式");return}
        if(!options.bindNetwork){reject("当前 CarPlay 模式需要绑定车机网络，请在设置中开启网络绑定");return}
        if(!BluetoothAdapter.checkBluetoothAddress(options.phoneMac)||options.phoneMac=="02:00:00:00:00:00"||options.phoneMac=="00:00:00:00:00:00"){
            reject("请在设置中填写手机真实蓝牙 MAC；系统占位地址不能作为协议身份");return
        }
        if(!BluetoothAdapter.checkBluetoothAddress(options.target)){reject("请先选择已配对车机");return}
        // Checked here so a disabled adapter fails before the host is bound and an audio route is requested.
        val adapter=context.getSystemService(BluetoothManager::class.java)?.adapter
        if(adapter==null||!adapter.isEnabled){reject("蓝牙未开启：请先在系统设置中打开蓝牙，再回到本页连接");return}
        job=scope.launch {
            var attempt=0
            while(isActive){
                if(attempt<Int.MAX_VALUE)attempt++
                if(!isActive)break
                val id=BridgeStore.begin(attempt)
                try { attempt(id,options,fromHost);break }
                catch(t:kotlinx.coroutines.CancellationException){throw t}
                catch(t:Exception){
                    currentCoroutineContext().ensureActive()
                    BridgeStore.log(id,"failure: "+t.javaClass.simpleName+" "+(t.message?:""))
                    // 空消息的异常（例如候选为空时抛的那条 IllegalStateException）只靠类型无法定位，把栈截断打出来。
                    BridgeStore.log(id,"failure stack: "+t.stackTraceToString().take(2048))
                    BridgeStore.log(id,ProtocolTrace.event(BridgeStore.state.value.stage.name,"session","local","attempt","failed",t.javaClass.simpleName))
                    val accessoryRejected=t is java.io.IOException&&t.message?.startsWith("Accessory rejected ")==true
                    // Digest 挑战是"此端点走不通"的确定信号，重试不会变好（见 DigestRequired）。
                    val terminalTransport=t is TransportException&&t.category in setOf(
                        TransportErrorCategory.PLATFORM_UNSUPPORTED,TransportErrorCategory.PERMISSION_DENIED,
                        TransportErrorCategory.INTERFACE_BIND_FAILED,
                        TransportErrorCategory.AUTH_FAILED,TransportErrorCategory.IDENTIFICATION_REJECTED)
                    val terminal=(t is IapStartupTimeout)||terminalTransport||t is PairUnsupported||t is SecurityException||t is IllegalArgumentException||t is IllegalStateException||
                        accessoryRejected||t is DigestRequired
                    if(terminal){
                        BridgeStore.update(id){it.copy(stage=Stage.FAILED,detail="在 "+it.stage.title+" 阶段失败",error=BridgeStore.redact(t.message?:t.javaClass.simpleName))}
                        break
                    }
                    BridgeStore.update(id){it.copy(stage=Stage.RETRY,detail="资源已释放，等待恢复连接",error=BridgeStore.redact(t.message?:"连接中断"))}
                    delay(options.retryIntervalSeconds*1000L)
                }
            }
        }
    }
    private suspend fun openLocalVideoContent(id:String,surface:Surface,width:Int,height:Int,fps:Int):LocalVideoContent? {
        val factory=localContent?:return null
        return try{factory.open(context,surface,width,height,fps)}
        catch(t:kotlinx.coroutines.CancellationException){throw t}
        catch(t:Throwable){BridgeStore.log(id,"Local display unavailable: "+t.javaClass.simpleName+" "+(t.message?:""));null}
    }
    private fun reject(s:String){val id=BridgeStore.begin(0);BridgeStore.update(id){it.copy(stage=Stage.FAILED,detail=s,error=s)};BridgeStore.log(id,s)}
    private suspend fun attempt(id:String,o:Options,fromHost:Boolean):Unit=withContext(Dispatchers.IO) {
        val r=Resources{trace->
            BridgeStore.log(id,"Resource close type="+trace.type+" elapsedMs="+trace.elapsedMs+" error="+trace.error)
        }
        val cleanup=SessionTermination{r.close()};termination=cleanup
        val failed=CompletableDeferred<Throwable>()
        val attemptJob=currentCoroutineContext().job
        val sessionScope=CoroutineScope(currentCoroutineContext())
        val ended=AtomicBoolean(false)
        val voiceToggle=r.own(VoiceButtonToggle())
        val receiverAudio=AtomicReference<List<AudioCapabilities.Entry>>(emptyList())
        val startAudio=AtomicReference<((Int,ByteArray,PcmFormat)->Boolean)?>(null)
        /** Siri/语音开始时按需建立 type100/speechRecognition（含麦克风输入）；固件没有启动预建。 */
        val startSpeech=AtomicReference<(() -> Boolean)?>(null)
        val observedAudio=ConcurrentHashMap.newKeySet<String>()
        val audio=r.own(HostAudioBridge(log={BridgeStore.log(id,it)}));audioBridge=audio
        val audioDemand=r.own(AudioDemandGate())
        val mediaPlayback=MediaPlaybackToggle()
        val frames=AtomicLong()
        val bytes=AtomicLong()
        val inputs=AtomicLong()
        val audioBytes=AtomicLong()
        val encoded=AtomicLong();val dropped=AtomicLong()
        val queueMs=AtomicLong();val writeMs=AtomicLong();val idr=AtomicLong()
        val idleRepeats=AtomicLong();val idleRepeatFailures=AtomicLong()
        var measuredAt=System.nanoTime();var measuredFrames=0L;var measuredBytes=0L;var measuredEncoded=0L
        val metrics=timer.scheduleAtFixedRate({
            val now=System.nanoTime();val f=frames.get();val b=bytes.get()
            val seconds=(now-measuredAt)/1_000_000_000.0
            val sound=audio.snapshot()
            if(!ended.get()&&seconds>0)BridgeStore.update(id){it.copy(frames=f,bytes=b,inputs=inputs.get(),audioBytes=audioBytes.get(),audioPackets=sound.received,audioUnsentPackets=sound.dropped,audioForwardedBytes=sound.forwardedBytes,microphoneBytes=sound.microphoneBytes,
                sentFps=(f-measuredFrames)/seconds,sentMbps=(b-measuredBytes)*8/seconds/1_000_000,
                encodedFps=(encoded.get()-measuredEncoded)/seconds,droppedFrames=dropped.get(),queueMs=queueMs.getAndSet(0),writeMs=writeMs.getAndSet(0),idrRequests=idr.get())}
            measuredAt=now;measuredFrames=f;measuredBytes=b;measuredEncoded=encoded.get()
        },1000,1000,TimeUnit.MILLISECONDS)
        // Cleanup must not run on the thread that observed the failure: failure() is reachable from
        // RTSP reader/event threads and from iAP readers, while AirSession.close() now has to send a
        // bounded whole-session TEARDOWN that waits for the control reader. Running that on the
        // reader thread itself stalls until the budget expires (observed as "InterruptedException"
        // on the TEARDOWN). Hand cleanup to its own thread so the caller can unwind its read loop.
        fun failure(t:Throwable){if(attemptJob.isActive&&!ended.get()&&failed.complete(t)){BridgeStore.log(id,"channel failure "+t.javaClass.simpleName+" "+(t.message?:"no message"));if(false)t.stackTrace.take(4).forEach{BridgeStore.log(id,"${"channel origin "}${it}")};Thread({runCatching{cleanup.close()}},"session-cleanup").apply{isDaemon=true;start()}}}
        suspend fun <T> phase(stage:Stage,millis:Long,block:suspend()->T):T {
            BridgeStore.update(id){it.copy(stage=stage,detail=stage.title,error=null)}
            BridgeStore.log(id,"stage "+stage.name)
            BridgeStore.log(id,ProtocolTrace.event(stage.name,"session","local","stage","start"))
            val timeout=timer.schedule({failure(java.net.SocketTimeoutException(stage.name+" deadline"))},millis,TimeUnit.MILLISECONDS)
            try {
                val result=block();if(failed.isCompleted)throw failed.await();return result
            }catch(t:Exception){
                currentCoroutineContext().ensureActive()
                // A channel may close resources while setup is still allocating them.
                // Preserve the initial failure instead of reporting the resulting Session closed.
                if(failed.isCompleted){
                    val original=failed.await()
                    if(original!==t)BridgeStore.log(id,"secondary setup error: "+t.javaClass.simpleName+" "+(t.message?:""))
                    throw original
                }
                throw t
            }finally{timeout.cancel(false)}
        }
        val phoneHasScreen=AtomicBoolean(true)
        // 自建投屏页：宿主没人接这个触摸时，事件要落到它上面。
        val localContentRef=AtomicReference<LocalVideoContent?>(null)
        val projectionGeometry=AtomicReference<ProjectionGeometry?>(null)
        val touchLock=Any()
        var touchClosed=false
        var pressed=false
        var downTime=0L
        var lastX=0f
        var lastY=0f
        val keyLock=Any()
        val musicLock=Any()
        val latestMusic=AtomicReference<NowPlayingUpdate.Track?>(null)
        val musicAir=AtomicReference<AirSession?>(null)
        fun deliverMusic(replaceMedia:Boolean=true){synchronized(musicLock){
            if(!ended.get())latestMusic.get()?.let{musicAir.get()?.nowPlaying(it,replaceMedia=replaceMedia)}
        }}
        fun deliverNavigation(fields:List<Pair<Int,ByteArray>>){
            if(ended.get())return
            val air=musicAir.get() ?: return
            if(!NavigationGuidance.active)return
            scope.launch(Dispatchers.IO){
                if(!air.navigationRouteUpdate(fields))
                    BridgeStore.log(id,"navigation 5201 update not sent")
            }
        }
        // Speech output activity is not proof that recognition is listening or has ended.
        // VoiceButtonToggle keeps local accepted requests until a verified host state is available.
        val heldKeys=mutableMapOf<Int,Long>()
        var keysClosed=false
        val pendingHostFps=AtomicInteger(0)
        var video:VideoEncoder?=null
        val h=r.own(hostFactory(context,object:HostCallbacks {
            override fun event(name:String,value:Int){
                if(ended.get())return
                BridgeStore.log(id,"host "+name+" "+value)
                when(name){
                    "host-display"->BridgeStore.update(id){it.copy(hostDisplay=value)}
                    "touch-listener"->BridgeStore.update(id){it.copy(touch=value==1)}
                    "host-binder-died","host-disconnected","host-binding-died","host-destroy","host-null-binding","host-bind-error"->failure(java.io.IOException(name))
                }
            }
            override fun pcm(data:ByteArray,category:Int,rate:Int,channels:Int,encoding:Int){
                if(ended.get())return
                audioBytes.addAndGet(data.size.toLong())
                audioProbeSamples.trySend(AudioProbeSample(category,rate,channels,data.size,data.any{it!=0.toByte()}))
                val pcmFormat=PcmFormat(rate,channels,encoding)
                val entries=receiverAudio.get()
                if(observedAudio.add("$category/$rate/$channels/$encoding")){
                    BridgeStore.log(id,"Audio host callback category=$category phase=first-format monoNs="+System.nanoTime()+
                        " bytes="+data.size+" source=$rate/$channels; before setup or queue admission")
                    val matches=AudioCapabilities.playback(entries,pcmFormat)
                    BridgeStore.log(id,"${"Audio category="}${category}${" PCM "}${rate}${" Hz channels="}${channels}${" playback matches="}"+matches.size+"; stream purpose and RTP profile still require verification")
                }
                if(startAudio.get()?.invoke(category,data,pcmFormat)!=true)audio.receive(data,category,pcmFormat)
            }
            override fun audioState(category:Int,state:Int){if(!ended.get()){
                audio.state(category,state)
                if(category==1)mediaPlayback.audioLaneActive(state==1)
                // category3 is an audio lane only. Prompt completion must not stop recognition.
            }}
            override fun music(info:HostMusic?){
                if(ended.get())return
                if(info==null){BridgeStore.log(id,"Host reported no current music item");return}
                BridgeStore.log(id,"${"Host music source="}${info.source}${" song="}${info.song}${" artist="}${info.artist}${" duration="}${info.duration}${" playlistSize="}${info.playlistSize}${" index="}${info.index}")
                BridgeStore.update(id){it.copy(hostMusic=BridgeStore.redact(
                    listOfNotNull(info.song,info.artist).filter{it.isNotBlank()}.joinToString(" - ").ifBlank{"(未命名)"}))}
                // The CarWith bridge exposes duration/index/progress as long/int values. The
                // current adapter treats them as the 5001 u32 millisecond/index fields, but
                // this unit mapping is an explicit local assumption until the same APK/vehicle
                // pair confirms it. Reject values outside the wire range instead of truncating.
                val track=NowPlayingUpdate.Track(
                    title=NowPlayingUpdate.textOrNull(info.song),artist=NowPlayingUpdate.textOrNull(info.artist),
                    durationMs=info.duration.takeIf{it in 1..0xffffffffL},
                    queueIndex=info.index.toLong().takeIf{it>=0},queueCount=info.playlistSize.toLong().takeIf{it>0})
                latestMusic.set(track)
                scope.launch(Dispatchers.IO){
                    runCatching{deliverMusic()}
                        .onFailure{BridgeStore.log(id,"nowplaying send failed: "+it.javaClass.simpleName)}
                }
            }
            override fun musicProgress(progress:Long){
                if(ended.get())return
                BridgeStore.update(id){it.copy(hostMusicProgress=progress)}
                if(progress in 0..0xffffffffL){
                    val old=latestMusic.get()?:NowPlayingUpdate.Track()
                    latestMusic.set(old.copy(elapsedMs=progress))
                    scope.launch(Dispatchers.IO){runCatching{deliverMusic()}.onFailure{
                        BridgeStore.log(id,"nowplaying progress send failed: "+it.javaClass.simpleName)
                    }}
                }else BridgeStore.log(id,"Host music progress outside u32 ignored: "+progress)
            }
            override fun optionalAction(intent:android.content.Intent){
                if(ended.get())return
                val action=intent.action?:"null"
                BridgeStore.update(id){it.copy(hostOptionalActions=it.hostOptionalActions+1)}
                BridgeStore.log(id,"Host action "+action+" extras="+intent.extras?.keySet()?.sorted()?.joinToString(","))
                if(action=="carlife_vehicle_music_info"){
                    val parsed=CarLifeMusicIntent.parse(intent)
                    if(parsed!=null){
                        latestMusic.set(parsed)
                        BridgeStore.log(id,"CarLife music Intent normalized for 5001: title="+
                            (parsed.title!=null)+" artist="+(parsed.artist!=null)+" album="+
                            (parsed.album!=null)+" duration="+(parsed.durationMs!=null)+
                            " elapsed="+(parsed.elapsedMs!=null))
                        // Intent payloads may be partial (for example progress-only); let the
                        // publisher merge them with its last accepted snapshot.
                        scope.launch(Dispatchers.IO){runCatching{deliverMusic(replaceMedia=false)}.onFailure{
                            BridgeStore.log(id,"CarLife music Intent send failed: "+it.javaClass.simpleName)
                        }}
                    }else BridgeStore.log(id,"CarLife music Intent had no recognized metadata fields")
                    if(CarLifeMusicIntent.hasArtwork(intent))
                        BridgeStore.log(id,"CarLife music artwork observed; 5001 artwork file transfer remains unimplemented")
                    return
                }
                when(action){
                    "carlife_show_hud_info"->{
                        val road=intent.getStringExtra("road_name")?:""
                        val remain=intent.getIntExtra("remain_distance",-1)
                        val components=NavigationGuidance.components
                        BridgeStore.update(id){it.copy(hostHud="${"kind="}${intent.getIntExtra("action",0)}${" turn="}${intent.getIntExtra("navi_turn",0)}${" remains="}${remain}${" total="}${intent.getIntExtra("total_distance",0)}${" road="}${road}")}
                        // Only fields whose CarWith names match the frozen firmware schema are
                        // translated. Product-specific action/turn enums stay diagnostic until
                        // their numeric mapping is captured from the same APK/vehicle pair.
                        val routeValues=NavigationGuidance.route(NavigationGuidance.RouteUpdate(
                            components=components,currentRoad=road.takeIf{it.isNotEmpty()},
                            distanceRemaining=remain.toLong().takeIf{it>=0}))
                        if(routeValues.isNotEmpty())deliverNavigation(routeValues)
                    }
                    "carlife_change_theme"->{
                        val mode=intent.getIntExtra("mode",-1)
                        BridgeStore.update(id){it.copy(hostNightMode=mode)}
                    }
                }
            }
            override fun musicSampleRate():Int?=audio.musicSampleRate()
            // Advertised capability alone cannot deliver microphone PCM to the host.
            override fun vehicleMicrophoneReady():Boolean{
                val hostMic=host?.capabilities()?.microphone==true
                val protocolMic=protocol.capabilities.microphone
                val carInput=activeAir?.microphoneInputAvailable()==true
                val inputReady=audio.microphoneReady()
                val ready=hostMic&&protocolMic&&carInput&&inputReady
                if(!micQueryLogged){micQueryLogged=true
                    BridgeStore.log(id,"CarWith mic query: host="+hostMic+" protocol="+protocolMic+
                        " carInput="+carInput+" inputReady="+inputReady+" -> "+ready)}
                return ready
            }
            override fun fps(value:Int){
                if(!ended.get()){
                    if(value<=0){BridgeStore.log(id,"${"Invalid host FPS request ignored: "}${value}");return}
                    BridgeStore.log(id,"${"Dynamic FPS requested="}${value}")
                    pendingHostFps.set(value)
                    applyDynamicFps?.invoke(value)
                }
            }
        }));host=h;audio.bindHost(h)
        // 协议能力：编排层按协议栈声明决策，不把 CarPlay 的能力当通用能力。
        val protocolCaps=protocol.capabilities
        BridgeStore.log(id,"protocol="+protocol.id+" video="+protocolCaps.video+" audio="+protocolCaps.audio+
            " microphone="+protocolCaps.microphone+" wirelessHandoff="+protocolCaps.wirelessHandoff)
        // 宿主能力：未声明（null）时按"全能力 + 不限 FPS"处理，保持既有行为。
        val caps=h.capabilities()?:HostCapabilities()
        if(!caps.touch||!caps.keys||!caps.microphone)
            BridgeStore.log(id,"host capabilities: touch="+caps.touch+" keys="+caps.keys+" microphone="+caps.microphone+" displays="+caps.displayCount)
        fun hostTouch(event:MotionEvent):Boolean =
            if(caps.touch&&protocolCaps.touch) runCatching{h.touch(event)}.getOrDefault(false) else false
        // 宿主键码映射由宿主模块提供；`:session` 只保留语义（媒体 usage、UI 事件前缀、语音起停）。
        val keyMapper=h.keyMapper()
        val keyAdapter=CarPlayKeyAdapter(keyMapper)
        /** CarWith 键码的按下/松开：CarPlay 事件映射与手动模拟共用同一条发送路径。 */
        var keysUnsupportedLogged=false
        fun sendHostKey(code:Int,down:Boolean):Boolean = synchronized(keyLock){
            if(ended.get()||keysClosed)return@synchronized false
            // 宿主或协议栈未声明按键能力时不投递，只记一次，避免每条事件都刷日志。
            if(!caps.keys||!protocolCaps.keys){
                if(!keysUnsupportedLogged){keysUnsupportedLogged=true
                    BridgeStore.log(id,"host or protocol does not accept key events; key dispatch disabled")}
                return@synchronized false
            }
            val now=SystemClock.uptimeMillis()
            val started=if(down)heldKeys[code]?:now else heldKeys[code]?:return@synchronized true
            val action=if(down)KeyEvent.ACTION_DOWN else KeyEvent.ACTION_UP
            val event=KeyEvent(started,now,action,code,0)
            val accepted=runCatching{h.key(event)}.getOrDefault(false)
            BridgeStore.log(id,"CarWith key code=$code action=${if(down)"DOWN" else "UP"} source=${event.source} accepted=$accepted")
            if(accepted){if(down)heldKeys[code]=started else heldKeys.remove(code);inputs.incrementAndGet()}
            accepted
        }
        /**
         * CarPlay protocol events are handled directly here.  The generic user binding/learning
         * sequence is intentionally bypassed: CarPlay usages have a protocol meaning and the
         * CarWith key contract is fixed, so a persisted binding must not change runtime behavior.
         * Events are still recorded while capture mode is active for diagnostics only.
         */
        // A single bounded consumer preserves car press order across both local backends.
        val mediaOutput=Channel<Pair<Int,Boolean>>(16)
        r.own(AutoCloseable{mediaOutput.cancel()})
        sessionScope.launch(Dispatchers.IO){
            for((code,system) in mediaOutput){
                if(ended.get())break
                try{
                    val accepted=if(system){
                        val manager=context.getSystemService(android.media.AudioManager::class.java)
                        if(manager==null)false else {
                            val at=SystemClock.uptimeMillis()
                            try{manager.dispatchMediaKeyEvent(KeyEvent(at,at,KeyEvent.ACTION_DOWN,code,0))}
                            finally{manager.dispatchMediaKeyEvent(KeyEvent(at,SystemClock.uptimeMillis(),KeyEvent.ACTION_UP,code,0))}
                            inputs.incrementAndGet();true
                        }
                    }else{
                        val down=sendHostKey(code,true)
                        val up=if(down)sendHostKey(code,false) else false
                        down&&up
                    }
                    BridgeStore.log(id,"HID press delivered; playback acceptance pending; code="+code+" systemRoute="+system+" delivered="+accepted)
                }catch(t:Exception){BridgeStore.log(id,"Media press dispatch failed code="+code+" "+t.javaClass.simpleName)}
            }
        }
        fun directHidUsage(eventId:String):Boolean{
            val prefix=when{
                eventId.startsWith("media:")->"media"
                eventId.startsWith("pageb:")->"pageb"
                else->return true
            }
            val usage=eventId.substringAfter(':').substringBefore(':').toIntOrNull(16)?:return false
            val down=eventId.endsWith(":down")
            // U2IW consumes Consumer/Telephony presses once; releases only update decoder state.
            if(!down)return true
            val systemCode=if(prefix=="media")keyAdapter.systemMediaUsage(usage)else null
            var useSystem=systemCode!=null
            val code=when{
                prefix=="media"&&usage==0xcd&&keyAdapter.mediaUsage(0xb0)!=null&&keyAdapter.mediaUsage(0xb1)!=null->
                    mediaPlayback.choose(requireNotNull(keyAdapter.mediaUsage(0xb0)),requireNotNull(keyAdapter.mediaUsage(0xb1))).also{
                        useSystem=false
                    }
                systemCode!=null->systemCode
                else->{
                    val mapped=keyAdapter.hidEvent(prefix,usage)?:return false
                    mediaPlayback.observeExplicitKey(usage)
                    mapped
                }
            }
            return mediaOutput.trySend(code to useSystem).isSuccess
        }
        /**
         * requestUI is a one-shot protocol action, rather than a user-configurable binding.
         * These three schemes are the CarWith actions documented by the existing bridge contract.
         * Unknown schemes stay diagnostic-only so a new CarPlay URL cannot press an unrelated key.
         */
        fun directUiRequest(eventId:String):Boolean{
            if(!eventId.startsWith("ui:"))return true
            val code=keyAdapter.uiEvent(eventId)?:return false
            val down=sendHostKey(code,true)
            val up=if(down)sendHostKey(code,false) else false
            return down&&up
        }
        // null toggles an accepted Siri activation; explicit manual START/STOP share order.
        val voiceOutput=Channel<Boolean?>(8)
        r.own(AutoCloseable{voiceToggle.close();voiceOutput.cancel()})
        sessionScope.launch(Dispatchers.IO){
            for(requestedStart in voiceOutput){
                if(ended.get())break
                val dispatchBegan=System.nanoTime()
                var dispatchOutcome="failed"
                BridgeStore.log(id,"Voice dispatch phase=begin requested="+(requestedStart?.toString()?:"toggle")+
                    " monoNs="+dispatchBegan)
                val dispatch:(Boolean)->Boolean={start->
                    keyMapper?.let{mapper->
                        val code=if(start)mapper.voiceStart() else mapper.voiceStop()
                        val down=sendHostKey(code,true)
                        val up=if(down)sendHostKey(code,false) else false
                        BridgeStore.log(id,"CarWith voice toggle key="+code+" downAccepted="+down+" cleanupUp="+up)
                        // CarWith acts on DOWN; failed UP cleanup must not misreport the opposite state.
                        down
                    }?:false
                }
                val accepted=try{
                    val result=if(requestedStart==null)voiceToggle.toggle(dispatch)
                        else voiceToggle.request(requestedStart,dispatch)
                    dispatchOutcome=if(result)"accepted" else "rejected"
                    result
                }finally{
                    BridgeStore.log(id,"Voice dispatch phase=end outcome=$dispatchOutcome elapsedMs="+(System.nanoTime()-dispatchBegan)/1_000_000+
                        "; local dispatch only, not host playback confirmation")
                }
                BridgeStore.log(id,"Voice local requestedActive="+voiceToggle.isRequestedActive+" hostRunningConfirmed=false requestAccepted="+accepted)
            }
        }
        fun directVoiceAction(action:String):Boolean{
            BridgeStore.log(id,"Voice trigger source=protocol action="+(action.toIntOrNull()?.toString()?:"unknown")+
                " monoNs="+System.nanoTime()+" speechSetupAvailable="+(startSpeech.get()!=null))
            BridgeStore.recordCarPlayKey(CarPlayEvents.voice(action))
            val raw=action.toIntOrNull()?:return false
            if(raw==2){
                val newSetup=startSpeech.get()?.invoke()
                BridgeStore.log(id,"Voice speech preparation newSetupRequested="+newSetup+
                    "; false may mean already prepared or request coalesced")
            }
            val accepted=voiceToggle.button(raw){voiceOutput.trySend(null).isSuccess}
            BridgeStore.log(id,"CarPlay Siri action="+raw+" adapterAccepted="+accepted+
                " localRequestedActive="+voiceToggle.isRequestedActive+" hostRunningConfirmed=false")
            return accepted
        }
        sendKey={code,down->
            val mapper=keyMapper
            if(mapper!=null&&(code==mapper.voiceStart()||code==mapper.voiceStop()))
                !ended.get()&&(!down||voiceOutput.trySend(code==mapper.voiceStart()).isSuccess)
            else sendHostKey(code,down)
        }
        /** Direct event dispatch; no generic binding table or sequence state is consulted. */
        fun onCarPlayEvent(eventId:String):Boolean{
            BridgeStore.recordCarPlayKey(eventId)
            return directHidUsage(eventId)&&directUiRequest(eventId)
        }
        // Close audio before host; the original ownership remains idempotent.
        r.own(AutoCloseable{audio.close()})
        // Reverse resource order releases held input before the host Binder closes,
        // including deadline and channel failures that close resources immediately.
        r.own(AutoCloseable {
            synchronized(keyLock){
                keysClosed=true
                for((code,down) in heldKeys)runCatching{h.key(KeyEvent(down,SystemClock.uptimeMillis(),KeyEvent.ACTION_UP,code,0))}
                heldKeys.clear()
            }
            synchronized(touchLock){
                touchClosed=true
                if(pressed){
                    val cancel=MotionEvent.obtain(downTime,SystemClock.uptimeMillis(),MotionEvent.ACTION_CANCEL,lastX,lastY,0).apply{source=InputDevice.SOURCE_TOUCHSCREEN}
                    try{runCatching{hostTouch(cancel)}}finally{cancel.recycle();pressed=false}
                }
            }
        })
        try{
            if(fromHost){
                phase(Stage.HOST,12000){
                    h.bind()
                    h.selectCarLifePlusAudio()
                    BridgeStore.log(id,"CarWith audio route requested immediately after host binding; preferred source PCM=48000 Hz; actual callback format remains authoritative")
                }
            }else BridgeStore.log(id,"Session not started by CarWith; the app-owned display keeps the encoder surface")
        // A 方案：CarPlay 的握手与会话构造收进 :protocol-carplay；媒体仍由本类驱动。
        val carPlayHost=object:CarPlayHost{
            override fun log(message:String)=BridgeStore.log(id,message)
            override fun touch(sample:TouchSample):Boolean=synchronized(touchLock){
                if(ended.get()||touchClosed||!phoneHasScreen.get())return@synchronized false
                val mapped=projectionGeometry.get()?.map(sample)?:return@synchronized false
                val now=SystemClock.uptimeMillis()
                val action=when{sample.pressed&&!pressed->{downTime=now;MotionEvent.ACTION_DOWN};sample.pressed->MotionEvent.ACTION_MOVE;pressed->MotionEvent.ACTION_UP;else->return@synchronized true}
                pressed=sample.pressed;lastX=mapped.x;lastY=mapped.y
                val event=MotionEvent.obtain(downTime,now,action,mapped.x,mapped.y,0).apply{source=InputDevice.SOURCE_TOUCHSCREEN}
                try{
                    val accepted=hostTouch(event)||localContentRef.get()?.touch(event)==true
                    inputs.incrementAndGet();accepted
                }finally{event.recycle()}
            }
            override fun key(prefix:String,usage:Int,down:Boolean):Boolean=onCarPlayEvent(CarPlayEvents.key(prefix,usage,down))
            override fun failure(cause:Throwable)=failure(cause)
            override fun runtimeChanged(state:RuntimeIapState){
                if(!ended.get())BridgeStore.update(id){it.copy(runtimeIap=when(state){
                    RuntimeIapState.WAITING_DATA->"等待车机数据"
                    RuntimeIapState.SYNCHRONIZING->"正在同步"
                    RuntimeIapState.LINK_READY->"链路已同步 · 业务交接未确认"
                    RuntimeIapState.AUTHENTICATING->"运行时链路重新识别与认证"
                    RuntimeIapState.CONTROL_READY->"运行时识别与实验验签完成 · 未验证信任链"
                    RuntimeIapState.DEGRADED->"已降级 · 保留蓝牙与视频"
                    RuntimeIapState.CLOSED->"已关闭"
                })}
            }
            override fun ui(url:String):Boolean{
                BridgeStore.update(id){it.copy(hostUiRequest=url)}
                return onCarPlayEvent(CarPlayEvents.ui(url))
            }
            override fun nightMode(mode:Int){
                if(ended.get())return
                BridgeStore.update(id){it.copy(hostNightMode=mode)}
                scope.launch{
                    val reply=h.invoke("carlife_change_theme"){it.putExtra("mode",mode)}
                    BridgeStore.log(id,"Car night mode="+mode+" forwarded as carlife_change_theme reply="+(reply!=null))
                }
            }
            override fun focusOffer(){
                onCarPlayEvent(CarPlayEvents.FOCUS)
                if(!ended.get())BridgeStore.log(id,"Car offered focus; host keys 8114/8115 need an on-device check, recording only")
            }
            override fun voice(action:String):Boolean=directVoiceAction(action)
            override fun warn(message:String){BridgeStore.update(id){s->s.copy(warning=BridgeStore.redact(message))}}
        }
        val runner=CarPlayRunner(context,o,r,carPlayHost)
            val bt=phase(Stage.BLUETOOTH,90000){runner.openBluetooth()}
            val pendingSourceEof=AtomicReference<Throwable?>(null)
            val sourceFailure=AtomicReference<(Throwable)->Unit>({error->
                if(generateSequence(error){it.cause}.any{it is java.io.EOFException})pendingSourceEof.compareAndSet(null,error)
                else failure(error)
            })
            val link=r.own(IapLink(bt.inputStream,bt.outputStream,{BridgeStore.log(id,it)},{sourceFailure.get().invoke(it)}))
            phase(Stage.DETECT,25000){link.start(allowDirectSyn=true)}
            val identity=PairStore(context).identity()
            val networkHandoff=r.own(IapNetworkHandoff(link.generation,link.linkEpoch,o.experiment,
                {attemptJob.isActive&&!ended.get()&&!failed.isCompleted&&
                    link.negotiatedControlSession!=null},
                {BridgeStore.log(id,it)}))
            // The selected control schema owns the transaction order. Authentication failure
            // never retries another order or reuses the same socket's security state.
            var bootstrap=phase(Stage.AUTH,90000){
                runner.negotiate(link,o.phoneMac,o.carPlayName,identity,lastBootstrap,
                    experimentalIntegrityOnly=o.experiment,
                    networkHandoff=networkHandoff,
                    onNowPlayingCommand={command,fields->
                        // 发布器在 AirSession 建好后才有；先暂存订阅，建立后由 AirSession 取走。
                        NowPlayingUpdate.pendingSubscription=if(command==NowPlayingUpdate.START)fields else null
                        true
                    })
            }
            val sourceAuthentication=requireNotNull(bootstrap.authentication)
            val sourceBinding=SecurityBinding(sourceAuthentication.generation,id,sourceAuthentication.epoch)
            val sourceIdentification=bootstrap.identification
            r.own(AutoCloseable{sourceIdentification?.invalidate()})
            val sourceContextCurrent=AtomicBoolean(true)
            r.own(link.bindEpoch(sourceBinding.epoch){
                sourceContextCurrent.set(false)
                sourceIdentification?.invalidate()
                failure(SecurityFailure(SecurityDiagnostic("iAP2","source-link-restart",SecurityReason.STALE_CONTEXT)))
            })
            if(!sourceContextCurrent.get())securityFailure(SecurityReason.STALE_CONTEXT,phase="source-link-restart")
            networkHandoff.acceptBootstrap(bootstrap)
            lastBootstrap=bootstrap
            val handoff=HandoffSupervisor()
            val sourceRef=HandoffSupervisor.ResourceRef(id+"-bt",1,link.linkEpoch)
            val targetRef=HandoffSupervisor.ResourceRef(id+"-airplay",1)
            val leaseRef=HandoffSupervisor.ResourceRef(id+"-network",1)
            // A session-local correlation token follows the chosen endpoint pipeline. Pair/AA still
            // verifies the actual peer; this token is not a claimed authenticated device identity.
            val peerCandidate=id
            handoff.arm(sourceRef,targetRef,peerCandidate,leaseRef,System.nanoTime()+150_000_000_000L,
                requiresTargetIap=false) // This wireless schema treats runtime iAP as optional.
            val cutoverTimer=timer.schedule({
                val snapshot=handoff.checkDeadline()
                if(snapshot.state==HandoffSupervisor.State.HANDOFF_FAILED)
                    failure(TransportException(TransportErrorCategory.HANDOFF_FAILED,TransportErrorCategory.HANDOFF_FAILED.name))
            },150000,TimeUnit.MILLISECONDS)
            r.own(AutoCloseable{cutoverTimer.cancel(false)})
            sourceFailure.set{error->
                val detached=handoff.snapshot.sourceDetached
                val eof=generateSequence(error){it.cause}.any{it is java.io.EOFException}
                if(detached||eof){
                    val snapshot=handoff.sourceDetach(sourceRef)
                    // Publish detachment before invalidating the handler: a concurrent
                    // consumer must not turn a stale identity callback into a fatal
                    // non-EOF source failure while the handoff is still in progress.
                    sourceIdentification?.invalidate()
                    if(snapshot.state==HandoffSupervisor.State.HANDOFF_FAILED)failure(error)
                    else {
                        if(!detached)BridgeStore.log(id,"Bluetooth source detached during explicit handoff; target readiness remains independent")
                        r.release(link);r.release(bt)
                    }
                }else failure(error)
            }
            pendingSourceEof.getAndSet(null)?.let{sourceFailure.get().invoke(it)}
            launch {
                fun checkSourceLink(){
                    check(sourceContextCurrent.get()&&link.generation==sourceBinding.generation&&
                        link.linkEpoch==sourceBinding.epoch){"Post-bootstrap iAP link changed"}
                    // poll owns terminal errors and preserves their cause (notably EOF,
                    // which the handoff supervisor may classify as source detachment).
                }
                try{while(isActive){
                    if(handoff.snapshot.sourceDetached)break
                    checkSourceLink()
                    val command=link.poll()
                    if(handoff.snapshot.sourceDetached)break
                    checkSourceLink()
                    command?.let{
                    val fields=it.fields
                    when{
                        sourceIdentification?.handle(it,link.generation,link.linkEpoch){message->BridgeStore.log(id,message)}==true->Unit
                        networkHandoff.handle(it,link.generation,link.linkEpoch)->Unit
                        fields!=null->BridgeStore.log(id,"Unsupported post-bootstrap Bluetooth iAP command "+it.id.toString(16))
                        // lingo 载荷不再是异常，也不丢弃：记录 id 与解析出的 lingo/command 后继续。
                        else->{val lingo=(it as IapCommand.Lingo).message;BridgeStore.log(id,"Post-bootstrap iAP lingo message id="+it.id.toString(16)+" lingo="+lingo.lingo+" command="+lingo.command.toString(16)+"; answer not implemented, recorded and continuing")}
                    }
                }}}
                catch(t:Exception){if(isActive&&!ended.get())sourceFailure.get().invoke(t)}
            }
            val networkReady=runner.prepareNetwork(bootstrap,networkHandoff){configuration->
                phase(Stage.WIFI,45000){runner.openNetwork(configuration,::failure)}
            }
            val network=networkReady.network
            bootstrap=networkReady.bootstrap
            lastBootstrap=bootstrap


            val air=runner.openSession(network,bootstrap,sourceBinding,VideoEncoder.supportedFps(),
                {sourceContextCurrent.get()&&!ended.get()&&!failed.isCompleted&&
                    link.linkEpoch==sourceBinding.epoch&&link.generation==sourceBinding.generation},
                controlPublication=networkReady.publication)
            activeAir=air
            // Publication precedes this check: disconnect either captures this
            // AirSession, or prevents its preparation after an earlier null snapshot.
            if(disconnecting)throw CancellationException("User disconnect before AirPlay preparation")
            musicAir.set(air)
            deliverMusic()
            air.screenOwnership={phone->synchronized(touchLock){
                if(ended.get()||touchClosed)return@synchronized false
                if(!phone&&pressed){
                    val cancel=MotionEvent.obtain(downTime,SystemClock.uptimeMillis(),MotionEvent.ACTION_CANCEL,lastX,lastY,0).apply{source=InputDevice.SOURCE_TOUCHSCREEN}
                    val accepted=try{hostTouch(cancel)}finally{cancel.recycle()}
                    if(!accepted)return@synchronized false
                    pressed=false
                }
                phoneHasScreen.set(phone)
                true
            }}
            air.requestKeyFrame={video?.requestIdr()?:false}
            val screen=phase(Stage.PAIR,90000){air.prepare{
                if(!ended.get())BridgeStore.update(id){it.copy(stage=Stage.SETUP,detail=Stage.SETUP.title,error=null)}
            }}
            handoff.targetAttach(targetRef,peerCandidate)
            check(handoff.airplayReady(targetRef).committed)
            cutoverTimer.cancel(false)

            receiverAudio.set(air.receiverAudio)
            BridgeStore.update(id){it.copy(receiverAudioEntries=air.receiverAudio.size)}
            phase(Stage.SETUP,15000){
                val activeScreen=screen
                if(activeScreen==null){
                    // 车机 /info 没给可用显示：跳过视频流、画面源与视频参数下发（docs §9.8 的降级）。
                    // 音频编排不依赖屏幕尺寸，它被放在本块之后，所以这条会话仍然能当音频端用。
                    BridgeStore.log(id,"receiver announced no usable display: this session sets up no video stream or touch binding; audio setup follows later")
                    return@phase
                }
                val format=h.format(activeScreen.width,activeScreen.height)
                val queriedWidth=if(format?.containsKey("width")==true)format.getInt("width") else activeScreen.width
                val queriedHeight=if(format?.containsKey("height")==true)format.getInt("height") else activeScreen.height
                val proportional=queriedWidth>0&&queriedHeight>0&&activeScreen.width.toLong()*queriedHeight==activeScreen.height.toLong()*queriedWidth
                val hostWidth=if(proportional)queriedWidth else activeScreen.width
                val hostHeight=if(proportional)queriedHeight else activeScreen.height
                if(!proportional&&format?.containsKey("width")==true&&format.containsKey("height"))BridgeStore.log(id,"${"CarWith encode suggestion "}${queriedWidth}${"x"}${queriedHeight}${" has different aspect ratio from receiver "}${activeScreen.width}${"x"}${activeScreen.height}${"; using receiver dimensions"}")
                BridgeStore.log(id,"${"Video geometry: receiver="}${activeScreen.width}${"x"}${activeScreen.height}${" host="}${hostWidth}${"x"}${hostHeight}${" proportional="}${proportional}")
                val geometry=ProjectionGeometry(activeScreen.width,activeScreen.height,hostWidth,hostHeight)
                projectionGeometry.set(geometry)
                // 帧率：接收端 maxFPS 与车机建议都只是上限，取较小者；编码器再夹一次。
                val receiverFps=activeScreen.fps
                val hostFpsHint=(format?.getInt("fps") ?: format?.getInt("maxFPS"))?.takeIf{it>0}
                val limit=minOf(receiverFps,hostFpsHint?:Int.MAX_VALUE)
                val supported=VideoEncoder.supportedFps(format)
                val fps=requireNotNull(supported(hostWidth,hostHeight,limit)){"No supported initial FPS"}
                BridgeStore.log(id,"Video limits: receiverFPS="+receiverFps+" hostFpsHint="+hostFpsHint+" limit="+limit+" chosen="+fps)
                // 码率：取双方候选里的**最高**；车机建议若基于更大的画布，先按像素比缩到实际编码尺寸。
                // 编码器的 bitrateRange 只用于夹取上限，永远不当候选值。
                val videoCeiling=VideoEncoder.supportedBitrate(format)?.last?.takeIf{it>0}
                val actualPixels=hostWidth.toLong()*hostHeight
                val hintWidth=format?.getInt("width")?.takeIf{it>0}
                val hintHeight=format?.getInt("height")?.takeIf{it>0}
                val hintPixels=if(hintWidth!=null&&hintHeight!=null)hintWidth.toLong()*hintHeight else actualPixels
                val hostHint=format?.takeIf{it.containsKey("bitrate")}?.getInt("bitrate")?.takeIf{it>0}
                val normalizedHint=hostHint?.let{raw->
                    if(hintPixels>0&&hintPixels!=actualPixels)(raw.toLong()*actualPixels/hintPixels).toInt() else raw
                }
                val nominal=nominalBitrate(hostWidth,hostHeight,fps)
                val candidates=listOfNotNull(normalizedHint,nominal)
                var bitrate=candidates.max()
                bitrate=videoCeiling?.let{bitrate.coerceAtMost(it)} ?: bitrate
                bitrate=bitrate.coerceAtLeast(MIN_BITRATE)
                BridgeStore.log(id,"Video bitrate="+bitrate+" candidates="+candidates+
                    " (hostHint="+hostHint+" normalized="+normalizedHint+" nominal="+nominal+
                    " hintPixels="+hintPixels+" actualPixels="+actualPixels+" codecCeiling="+videoCeiling+")")
                fun makeEncoder(rate:Int)=VideoEncoder(hostWidth,hostHeight,rate,bitrate,format,r,{b,config,pts->air.send(b,config,pts)},{n->
                    val count=frames.incrementAndGet();bytes.addAndGet(n.toLong())
                    if(count==1L&&!ended.get())BridgeStore.update(id){
                        if(it.stage==Stage.WAIT_FRAME)it.copy(stage=Stage.STREAMING,frames=count,bytes=bytes.get(),detail="首个视频帧已写入通道；车机画面、触摸和持续运行尚待实机确认") else it
                    }
                },::failure,{name,value->when(name){
                    "encoded"->encoded.addAndGet(value)
                    "dropped"->dropped.addAndGet(value)
                    "idr"->idr.addAndGet(value)
                    "bitrate-applied"->{
                        BridgeStore.update(id){it.copy(targetBitrate=value.toInt())}
                        BridgeStore.log(id,"Encoder bitrate parameter accepted="+value+"; actual output measured separately")
                    }
                    "bitrate-rejected"->BridgeStore.log(id,"Encoder rejected dynamic bitrate="+value+"; keeping current session")
                    "idr-rejected"->BridgeStore.log(id,"Encoder rejected sync-frame parameter; awaiting periodic IDR")
                    "queue-ms"->queueMs.updateAndGet{maxOf(it,value)}
                    "write-ms"->writeMs.updateAndGet{maxOf(it,value)}
                    // Logged once per session: one line proves the heartbeat runs, while a line per
                    // second of a still picture would bury everything else.
                    "idle-repeat"->if(idleRepeats.getAndIncrement()==0L)BridgeStore.log(id,"still picture: encoder has no output, resending the last frame every second to keep the media stream alive")
                    "idle-repeat-failed"->if(idleRepeatFailures.getAndIncrement()==0L)BridgeStore.log(id,"still-picture resend failed: the frame source cannot resubmit the current frame")
                    "front-surface-on"->BridgeStore.log(id,"encoder front surface established; it resends P frames for still pictures")
                    "front-surface-off"->BridgeStore.log(id,"encoder front surface not established; frame source feeds the encoder directly")
                    "front-surface-rejected"->BridgeStore.log(id,"device refused the encoder front surface; frame source feeds the encoder directly")
                    "front-surface-draw-failed"->BridgeStore.log(id,"drawing into the encoder front surface failed; stopped repeating the log")
                    else->VideoDiagnosticLog.message(name,value)?.let{BridgeStore.log(id,it)}
                }},stopSend={air.closeVideo()},
                    // Opt-in latency trade: the front surface is the only way a still CarWith picture
                    // gets a P frame, and it costs a blit per frame plus a few frames of latency.
                    frontSurface=o.frontSurface&&fromHost)
                val v=r.own(makeEncoder(fps));video=v
                BridgeStore.log(id,"${"AVC selected name="}${v.encoderName}${" hardware="}${v.hardwareAccelerated}${" size="}${hostWidth}${"x"}${hostHeight}${" fps="}${fps}${" bitrate="}${v.initialBitrate}")
                BridgeStore.update(id){it.copy(width=hostWidth,height=hostHeight,targetFps=fps,maxFps=limit,targetBitrate=v.initialBitrate)}
                v.start()
                // Observation only, once per session: ask the host what it offers and record the replies.
                // Neither answer changes local behaviour yet - they are here to be read off a real car.
                sessionScope.launch{
                    val opengl=h.invoke("use_carlife_opengl")
                    BridgeStore.log(id,"Host opengl reply keys="+(opengl?.keySet()?.sorted()?.joinToString(",")?:"null"))
                    val device=h.invoke("carlife_request_device_id")
                    device?.getString("device_id")?.let{BridgeStore.log(id,"Host device_id="+BridgeStore.redact(it))}
                }
                // The app owns the surface first: splash, then either the host or our own page.
                val local=openLocalVideoContent(id,v.surface,hostWidth,hostHeight,fps)
                if(local!=null){
                    local.show(LocalVideoPhase.SPLASH)
                    BridgeStore.log(id,"${"Splash page shown for "}${SPLASH_MILLIS}${"ms; hostExpected="}${fromHost}")
                    delay(SPLASH_MILLIS)
                    if(fromHost)runCatching{local.close()}
                    else{
                        // No host takes the surface, so the app-owned page stays for the whole session.
                        r.own(local);local.show(LocalVideoPhase.SCREEN)
                        // 画面留在这里，触摸的落点也登记上：宿主没人接时事件会落到这张页面上。
                        localContentRef.set(local)
                        // This page repaints on request, which is exactly what keeps the media stream
                        // alive while it stays still - and it never needed a front surface for that.
                        v.repeatFrame={local.heartbeat()}
                    }
                }else if(!fromHost){
                    // Neither a host nor an app-owned display: nothing can ever produce a frame, so
                    // report the real reason now instead of waiting for the first-frame deadline.
                    error("本地画面不可用：无法创建私有虚拟屏，请查看日志中的 Local display unavailable")
                }
                if(fromHost){
                    // The host renders into whatever surface it is handed and never repaints on its own,
                    // so it renders into the encoder's front surface: that is the only way a still host
                    // picture gets back into the encoder.
                    BridgeStore.log(id,if(o.frontSurface)"CarWith host owns the frame source; still pictures are resent via the encoder front surface" else "CarWith host owns the frame source; front surface disabled, so no P frames while still (latency first)")
                    h.surface(v.surface,hostWidth,hostHeight,o.dpi)
                }
                // Both paths own the encoder surface at this point, so both must advance the stage;
                // previously only the host path did, which left sessions without CarWith stuck on SETUP.
                // MediaCodec may emit the first frame synchronously from start().  If that
                // happens before this stage handoff, the frame callback has already counted it
                // while the state was still SETUP, so the old `frames == 0` guard left the UI in
                // SETUP/"connecting" forever even though the car was already showing video.
                // Publish the terminal state for that early frame here; later frames are handled
                // by the callback above while WAIT_FRAME is visible.
                BridgeStore.update(id){state ->
                    if(frames.get()==0L)state.copy(stage=Stage.WAIT_FRAME,detail="编码器已就绪，等待首个视频帧写入通道")
                    else state.copy(stage=Stage.STREAMING,detail="首个视频帧已写入通道；车机画面、触摸和持续运行尚待实机确认")
                }
                val encoderLock=Mutex()
                applyBitrate={requested->
                    sessionScope.launch(Dispatchers.IO){
                        encoderLock.lock()
                        try{
                            if(!ended.get()){
                                if(video?.setBitrate(requested)==true){bitrate=requested;BridgeStore.log(id,"Bitrate queued="+requested)}
                                else BridgeStore.log(id,"Bitrate not applied: encoder unavailable or unsupported")
                            }
                        }finally{encoderLock.unlock()}
                    }
                }
                var currentFps=fps
                val requestRevision=AtomicLong()
                applyDynamicFps={requested ->
                    val revision=requestRevision.incrementAndGet()
                    sessionScope.launch(Dispatchers.IO){
                        delay(500)
                        encoderLock.lock()
                        try{
                            if(revision!=requestRevision.get()||ended.get())return@launch
                            // 宿主声明了最大帧率时先夹到该上限，再交给编码器支持表。
                            val bounded=caps.maxFps?.let{minOf(requested,it)}?:requested
                            val target=supported(hostWidth,hostHeight,bounded.coerceIn(1,limit))
                            if(target==null||target==currentFps)return@launch
                            val encoder=video?:return@launch
                            if(encoder.setFrameRate(target)){
                                currentFps=target
                                BridgeStore.update(id){it.copy(targetFps=target)}
                                BridgeStore.log(id,"${"Dynamic FPS parameter applied="}${target}${"; existing Surface and CarWith session retained"}")
                            }else BridgeStore.log(id,"${"Dynamic FPS unsupported by encoder; keeping "}${currentFps}${" FPS and existing Surface"}")
                        }catch(t:kotlinx.coroutines.CancellationException){throw t}
                        catch(t:Exception){BridgeStore.log(id,"${"Dynamic FPS parameter failed; keeping "}${currentFps}${" FPS: "}"+(t.message?:t.javaClass.simpleName))}
                        finally{encoderLock.unlock()}
                    }
                }
                pendingHostFps.get().takeIf{it>0}?.let{applyDynamicFps?.invoke(it)}

            }
            // Existing prewarm/demand policy; this is not a recovered firmware scheduling rule.
            // 这一档要容纳音频 SETUP 的 RTSP 往返：控制连接允许等 60 s（S-0121），所以这里必须比它长，
            // 否则 phase 会先判失败、socket 的 60 s 永远用不上。代价是这个阶段真失败时也要等更久。
            phase(Stage.SETUP,70000){
                val completions=ConcurrentHashMap<Int,CompletableDeferred<Unit>>()
                fun requestAudio(category:Int,firstPcm:ByteArray,pcmFormat:PcmFormat,prime:Boolean=false):Boolean {
                    val ticket=if(prime)audioDemand.prime(category,pcmFormat)
                        else audioDemand.claim(category,firstPcm.size,pcmFormat)
                    if(ticket!=null){
                        BridgeStore.log(id,"Audio activation category=$category phase=queued prime=$prime firstPcmBytes="+
                            firstPcm.size+" monoNs="+System.nanoTime())
                        val completed=CompletableDeferred<Unit>()
                        completions[category]=completed
                        val initial=firstPcm.copyOf()
                        val capturedAt=ticket.capturedAtNs
                        sessionScope.launch(Dispatchers.IO){
                            val setupBegan=System.nanoTime()
                            var setupOutcome="incomplete"
                            BridgeStore.log(id,"Audio activation category=$category phase=begin monoNs=$setupBegan")
                            try{
                                val transport=air.createAudio(category,pcmFormat){pcm,format->audio.microphone(pcm,format)}
                                if(!audioDemand.install(ticket,transport,audio::attach)){
                                    setupOutcome="not-installed";return@launch
                                }
                                setupOutcome="installed"
                                // Do not replay a short prompt after a slow network negotiation.
                                if(initial.isNotEmpty()){
                                    if(System.nanoTime()-capturedAt<=100_000_000L)audio.receive(initial,category,pcmFormat)
                                    else BridgeStore.log(id,"${"Audio category="}${category}${" first PCM expired during SETUP; awaiting fresh source"}")
                                }
                                BridgeStore.update(id){it.copy(audioStatus="音频通道 ${audio.categories().sorted()} 已建立 · 编码/传输见日志 · 发声待实测")}
                            }catch(t:kotlinx.coroutines.CancellationException){setupOutcome="cancelled";throw t}
                            catch(t:Exception){
                                setupOutcome="failed:"+t.javaClass.simpleName
                                BridgeStore.log(id,"${"CarPlay audio category="}${category}${" unavailable; other streams retained: "}"+t.javaClass.simpleName+" "+(t.message?:""))
                                BridgeStore.update(id){it.copy(audioStatus="音频通道 ${audio.categories().sorted()}；分类 $category 未启用："+(t.message?:t.javaClass.simpleName))}
                            }finally{
                                audioDemand.failed(ticket);completed.complete(Unit)
                                BridgeStore.log(id,"Audio activation category=$category phase=end outcome=$setupOutcome elapsedMs="+
                                    (System.nanoTime()-setupBegan)/1_000_000)
                            }
                        }
                    }
                    return ticket!=null
                }
                // Retain the existing serialized prewarm order while testing SETUP field changes.
                val plan=air.bootstrapAudioPlan()
                BridgeStore.log(id,"Audio bootstrap plan="+plan.joinToString(","){
                    "cat="+it.route.category+" type="+it.route.type+"/"+it.route.purpose+" codec="+it.format.codec
                }.ifEmpty{"empty"})
                for(selection in plan){
                    val category=selection.route.category
                    requestAudio(category,byteArrayOf(),selection.format.decodedPcm,prime=true)
                    // 串行：等这一条 SETUP 完成（或失败/超时）再建下一条。
                    withTimeoutOrNull(6000){completions[category]?.await()}
                }
                startAudio.set{category,pcm,format->requestAudio(category,pcm,format)}
                startSpeech.set{requestAudio(3,byteArrayOf(),PcmFormat(24000,1),prime=true)}
                BridgeStore.update(id){it.copy(audioStatus="音频通道 ${audio.categories().sorted()} 已建立 · 发声待实测")}
            }
            // A receiver may legitimately expose only audio/control. In that mode no video
            // encoder exists and a first-frame watchdog would turn the documented downgrade into
            // a false session failure.
            val firstFrameDeadline=video?.let{timer.schedule({if(frames.get()==0L)failure(java.net.SocketTimeoutException("No video frame written"))},15000,TimeUnit.MILLISECONDS)}
            try{throw failed.await()}finally{firstFrameDeadline?.cancel(false)}
        } finally {
            ended.set(true);voiceToggle.close();startAudio.set(null);startSpeech.set(null);audioDemand.close();metrics.cancel(false);applyDynamicFps=null;applyBitrate=null;sendKey=null;carPlayAudioTestJob?.cancel();carPlayAudioTestJob=null;carWithAudioProbeJob?.cancel();carWithAudioProbeJob=null
            cleanup.close()
            withContext(NonCancellable){cleanup.awaitClosed()}
            if(termination===cleanup)termination=null
            if(host===h)host=null;if(audioBridge===audio)audioBridge=null;activeAir=null
            BridgeStore.log(id,"session resources released")
        }
    }
    override fun startCarWithAudioProbe(){
        if(carWithAudioProbeJob?.isActive==true)return
        val id=BridgeStore.state.value.id
        if(BridgeStore.state.value.stage!=Stage.STREAMING){BridgeStore.log(id,"CarWith audio probe rejected: session is not streaming");return}
        val h=host?:run{BridgeStore.log(id,"CarWith audio probe rejected: host unavailable");return}
        while(audioProbeSamples.tryReceive().isSuccess){}
        carWithAudioProbeJob=scope.launch(Dispatchers.IO){
            var mediaPackets=0L;var mediaBytes=0L;var nonzeroPackets=0L;var format:String?=null
            val categories=linkedSetOf<Int>()
            try{
                BridgeStore.update(id){it.copy(carWithAudioProbeRunning=true,carWithAudioProbeStatus="等待真实媒体 PCM 10 秒 · 请在手机播放音乐")}
                h.selectCarLifePlusAudio()
                val success=withTimeoutOrNull(10_000){
                    while(true){
                        val sample=audioProbeSamples.receive();categories+=sample.category
                        if(sample.category==1){
                            mediaPackets++;mediaBytes+=sample.bytes;if(sample.nonzero)nonzeroPackets++
                            format="${sample.rate}/${sample.channels}/PCM16"
                            if(mediaPackets>=10&&nonzeroPackets>0)return@withTimeoutOrNull true
                        }
                    }
                }==true
                if(success){
                    val message="已收到 CarWith 媒体 PCM：$format · $mediaPackets 包 · $mediaBytes 字节 · 非零 $nonzeroPackets 包"
                    BridgeStore.log(id,"${"CarWith audio probe success format="}${format}${" packets="}${mediaPackets}${" bytes="}${mediaBytes}${" nonzero="}${nonzeroPackets}${" categories="}${categories.joinToString()}")
                    BridgeStore.update(id){it.copy(carWithAudioProbeStatus=message)}
                }else{
                    val message="未收到可用媒体 PCM · 已见分类 "+(categories.joinToString().ifEmpty{"无"})
                    BridgeStore.log(id,"${"CarWith audio probe timeout mediaPackets="}${mediaPackets}${" bytes="}${mediaBytes}${" nonzero="}${nonzeroPackets}${" categories="}${categories.joinToString()}")
                    BridgeStore.update(id){it.copy(carWithAudioProbeStatus=message)}
                }
            }catch(t:CancellationException){throw t}
            catch(t:Exception){BridgeStore.log(id,"${"CarWith audio probe failed: "}${t.javaClass.simpleName}${" "}${t.message?:""}");BridgeStore.update(id){it.copy(carWithAudioProbeStatus="测试失败："+(t.message?:t.javaClass.simpleName))}}
            finally{BridgeStore.update(id){it.copy(carWithAudioProbeRunning=false)}}
        }
    }
    override fun toggleCarPlayAudioTest(){
        val current=carPlayAudioTestJob
        if(current?.isActive==true){current.cancel();return}
        val id=BridgeStore.state.value.id
        if(BridgeStore.state.value.stage!=Stage.STREAMING){BridgeStore.log(id,"CarPlay audio test rejected: session is not streaming");return}
        val air=activeAir?:run{BridgeStore.log(id,"CarPlay audio test rejected: AirPlay session unavailable");return}
        carPlayAudioTestJob=scope.launch(Dispatchers.IO){
            var direct:NegotiatedAudioTransport?=null
            try{
                BridgeStore.update(id){it.copy(carPlayAudioTestRunning=true,carPlayAudioTestStatus="正在建立独立 CarPlay 测试音")}
                val bridge=audioBridge
                val existing=bridge?.testFormat(1)
                val format=existing?:run{direct=air.createAudio(1,PcmFormat(48000,2),null);requireNotNull(direct).formats.getValue(1)}
                val frames=(format.rate/50).coerceAtLeast(1);var sample=0L
                BridgeStore.log(id,"CarPlay audio test begin route="+(if(existing!=null)"active-media"else "independent-media")+"${" PCM="}${format.rate}${"/"}${format.channels}${" left=440Hz right=660Hz"}")
                BridgeStore.update(id){it.copy(carPlayAudioTestStatus="发送左右声道测试音 6 秒 · 左 440 Hz / 右 660 Hz")}
                repeat(300){chunk->
                    currentCoroutineContext().ensureActive()
                    val out=ByteBuffer.allocate(frames*format.channels*2).order(ByteOrder.LITTLE_ENDIAN)
                    repeat(frames){index->
                        val pos=sample+index;val edge=minOf((chunk+1)/10.0,(300-chunk)/10.0,1.0)
                        val left=(sin(2*PI*440.0*pos/format.rate)*3600*edge).toInt().toShort();val right=(sin(2*PI*660.0*pos/format.rate)*3600*edge).toInt().toShort()
                        if(format.channels==1)out.putShort(((left.toInt()+right.toInt())/2).toShort())else{out.putShort(left);out.putShort(right)}
                    }
                    val sent=if(direct!=null){direct!!.send(1,out.array(),format);true}else bridge?.sendTest(1,out.array(),format)==true
                    check(sent){"Media audio transport unavailable"};sample+=frames;delay(20)
                }
                delay(300);BridgeStore.log(id,"${"CarPlay audio test source complete chunks=300 samples="}${sample}${"; audible confirmation pending"}")
                BridgeStore.update(id){it.copy(carPlayAudioTestStatus="测试数据已发送 · 请确认车机是否听到左右声道")}
            }catch(t:CancellationException){BridgeStore.update(id){it.copy(carPlayAudioTestStatus="测试音已停止")};throw t}
            catch(t:Exception){BridgeStore.log(id,"${"CarPlay audio test failed: "}${t.javaClass.simpleName}${" "}${t.message?:""}");BridgeStore.update(id){it.copy(carPlayAudioTestStatus="测试失败："+(t.message?:t.javaClass.simpleName))}}
            finally{direct?.close();BridgeStore.update(id){it.copy(carPlayAudioTestRunning=false)}}
        }
    }
    override suspend fun disconnect(){
        if(disconnecting)return
        disconnecting=true
        val id=BridgeStore.state.value.id
        val stoppedJob=job;val stoppedCleanup=termination
        val normalStop=stoppedCleanup?.beginNormalStop()==true
        val stoppedAir=activeAir
        BridgeStore.log(id,"User disconnect; whole-session stop requested before local cleanup")
        try{
            // Socket/codec cleanup must not block the UI; cancellation cannot skip cleanup.
            withContext(NonCancellable+Dispatchers.IO){
                try{
                    if(normalStop)stoppedAir?.stopNormally()
                }finally{
                    stoppedJob?.cancel()
                    stoppedCleanup?.finishNormalStop()
                    stoppedJob?.join()
                    stoppedCleanup?.awaitClosed()
                }
            }
            BridgeStore.idle()
        }finally{
            // Keep the start guard until cancellation and resource teardown complete.
            if(stoppedJob!=null&&!stoppedJob.isCompleted)stoppedJob.invokeOnCompletion{disconnecting=false}
            else disconnecting=false
        }
    }
    /** 手动模拟一个 CarWith 键码：与 CarPlay 映射走同一条发送路径，一次完整短按。 */
    override fun triggerCarWithKey(code:Int) {
        scope.launch(Dispatchers.IO){
            val sender=sendKey?:return@launch
            runCatching{sender(code,true);sender(code,false)}
        }
    }
    /** Integration boundary for a real established downstream audio stream, never a fake readiness flag. */
    /** Host actions whose inputs do not exist on our side yet. The entry points live here so a future
     *  status source can use them; nothing invents a value today, because a wrong "driving" flag would
     *  put the host into its restricted UI mode. */
    suspend fun notifyDrivingStatus(driving:Boolean):Boolean{
        val host=host?:return false
        return host.invoke("carlife_other_notify_driving_status"){
            it.putExtra("params",org.json.JSONObject().put("driving_status",driving.toString()).toString())}!=null
    }
    suspend fun notifyVehicleChannel(channel:String):Boolean{
        val host=host?:return false
        return host.invoke("carlife_notify_vehicle_channel"){
            it.putExtra("params",org.json.JSONObject().put("vehicle_channel",channel).toString())}!=null
    }
    suspend fun attachAudioTransport(transport:NegotiatedAudioTransport){
        val audio=audioBridge
        if(audio==null){runCatching{transport.close()};error("No active audio session")}
        audio.attach(transport)
    }
    suspend fun deliverMicrophone(pcm:ByteArray,format:PcmFormat):Boolean=audioBridge?.microphone(pcm,format)?:false
    override fun setVideoBitrate(value:Int){
        require(value>0)
        applyBitrate?.invoke(value)?:BridgeStore.log(BridgeStore.state.value.id,"Bitrate saved for next connection")
    }
    override fun close(){applyBitrate=null;applyDynamicFps=null;carPlayAudioTestJob?.cancel();carWithAudioProbeJob?.cancel();job?.cancel();termination?.forceClose();activeAir=null;audioBridge=null;scope.cancel();timer.shutdownNow()}
}
