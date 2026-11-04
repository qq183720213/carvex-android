package io.github.iamr0s.carvex.carplay.core
import java.io.*
import java.util.Locale

data class RtspMessage(val first:String,val headers:Map<String,String>,val body:ByteArray) {
    val status:Int get()=first.split(' ').getOrNull(1)?.toIntOrNull()?:0
}
class RecordInput(private val input:InputStream,private val key:ByteArray):InputStream(){
    internal var diagnostics:ControlReadDiagnostics?=null
    private var buffer=byteArrayOf(); private var pos=0; private var counter=0L
    private var failed=false
    @Synchronized override fun read():Int {
        check(!failed)
        if(pos==buffer.size)try{
            check(counter<Long.MAX_VALUE)
            diagnostics?.record("header",2)
            val h=IapWire.exact(input,2)
            val n=(h[0].toInt() and 255) or ((h[1].toInt() and 255) shl 8)
            require(n in 1..16384)
            // No plaintext or next nonce becomes visible until the whole tag has verified.
            diagnostics?.record("ciphertext",n+16)
            val ciphertext=IapWire.exact(input,n+16)
            diagnostics?.record("authenticate")
            val plaintext=Crypto.open(key,Crypto.nonce(counter),ciphertext,h)
            counter++;buffer=plaintext;pos=0
            diagnostics?.record("buffered")
        }catch(t:Exception){failed=true;runCatching{input.close()};throw t}
        return buffer[pos++].toInt() and 255
    }
    @Synchronized override fun read(b:ByteArray,off:Int,len:Int):Int {require(off>=0&&len>=0&&off<=b.size-len);if(len==0)return 0;val first=read();b[off]=first.toByte();val n=minOf(len-1,buffer.size-pos);buffer.copyInto(b,off+1,pos,pos+n);pos+=n;return n+1}
    override fun close(){failed=true;input.close()}
}
class RecordOutput(private val output:OutputStream,private val key:ByteArray):OutputStream(){
    private var counter=0L
    private var failed=false
    override fun write(b:Int)=write(byteArrayOf(b.toByte()))
    @Synchronized override fun write(b:ByteArray,off:Int,len:Int){
        check(!failed);require(off>=0&&len>=0&&off<=b.size-len)
        try{var p=off;while(p<off+len){
            check(counter<Long.MAX_VALUE)
            val n=minOf(1024,off+len-p);val h=byteArrayOf(n.toByte(),(n ushr 8).toByte())
            val record=h+Crypto.seal(key,Crypto.nonce(counter),b.copyOfRange(p,p+n),h)
            counter++ // The nonce is consumed even if a partial transport write fails.
            output.write(record);p+=n
        }}catch(t:Exception){failed=true;runCatching{output.close()};throw t}
    }
    @Synchronized override fun flush(){check(!failed);try{output.flush()}catch(t:Exception){failed=true;runCatching{output.close()};throw t}}
    override fun close(){failed=true;output.close()}
}
object RtspWire {
    private val headerName=Regex("[!#$%&'*+.^_`|~0-9A-Za-z-]+")
    fun read(input:InputStream):RtspMessage=read(input,null)
    internal fun read(input:InputStream,diagnostics:ControlReadDiagnostics?):RtspMessage {
        diagnostics?.rtsp("header")
        val out=ByteArrayOutputStream(); var matched=0
        val marker=byteArrayOf(13,10,13,10)
        while(matched<4){val b=input.read();if(b<0)throw EOFException("RTSP header");require(out.size()<16384);out.write(b);matched=if(b==marker[matched].toInt())matched+1 else if(b==13)1 else 0}
        val lines=out.toByteArray().toString(Charsets.US_ASCII).split("\r\n")
        require(lines[0].startsWith("RTSP/1.0 ")||lines[0].startsWith("HTTP/1.1 ")||lines[0].startsWith("HTTP/1.0 ")||Regex("^[A-Z_]+ \\S+ (RTSP/1.0|HTTP/1.[01])$").matches(lines[0]))
        if(lines[0].startsWith("RTSP/")||lines[0].startsWith("HTTP/")){
            val status=lines[0].split(' ').getOrNull(1)
            require(status!=null&&status.length==3&&status.all{it in '0'..'9'}&&status.toInt() in 100..599)
        }
        val headers=linkedMapOf<String,String>()
        lines.drop(1).filter{it.isNotEmpty()}.forEach {val i=it.indexOf(':');require(i>0);val key=it.substring(0,i).lowercase(Locale.ROOT);require(headerName.matches(key)&&key !in headers);val value=it.substring(i+1).trim();require(value.none{ch->ch.isISOControl()&&ch!='\t'});headers[key]=value}
        require("transfer-encoding" !in headers) { "Chunked RTSP unsupported" }
        val n=headers["content-length"]?.toIntOrNull()?:if("content-length" in headers)error("Invalid body length")else 0
        require(n in 0..4*1024*1024)
        diagnostics?.rtsp("body",n)
        val body=IapWire.exact(input,n)
        diagnostics?.rtsp("complete")
        return RtspMessage(lines[0],headers,body)
    }
    fun write(output:OutputStream,first:String,headers:Map<String,String>,body:ByteArray=byteArrayOf()){
        require(!first.contains('\r')&&!first.contains('\n'))
        require(headers.keys.none{it.equals("Content-Length",ignoreCase=true)})
        require(headers.keys.all{headerName.matches(it)})
        val h=buildString{append(first).append("\r\n");headers.forEach{(k,v)->require(!k.contains('\r')&&!v.contains('\r')&&!k.contains('\n')&&!v.contains('\n'));append(k).append(": ").append(v).append("\r\n")};append("Content-Length: ").append(body.size).append("\r\n\r\n")}
        output.write(h.toByteArray(Charsets.US_ASCII));output.write(body);output.flush()
    }
}
class RtspClient(input:InputStream,var output:OutputStream,
    private val event:(RtspMessage)->Pair<Int,ByteArray> = {501 to byteArrayOf()}) {
    private val readProgress=ControlReadDiagnostics()
    var input:InputStream=readProgress.raw(input)
    /** Approximate observations; raw arrival means a socket read returned, not wire arrival. */
    fun readDiagnostics(nowNanos:Long=System.nanoTime()):String=readProgress.snapshot(nowNanos)
    /** For bounded, on-demand thread-stack sampling only; do not interrupt or join this thread. */
    fun diagnosticReaderThread():Thread?=reader
    enum class Phase { SEND, RESPONSE, FAILED }
    class StatusException(val status:Int,method:String,path:String):IllegalStateException("RTSP $method $path status $status")
    /** Metadata only: bodies, headers, identities and pairing errors are not recorded here. */
    data class Exchange(val phase:Phase,val method:String,val path:String,val cseq:Int,
        val bodyBytes:Int,val elapsedMs:Long,val status:Int?=null,val error:String?=null,
        /** 等这把锁花了多久：请求之间是串行的，排队时间不计入 elapsedMs。 */
        val lockWaitMs:Long=0,
        /** /command 的 plist type，用来定位是哪条命令把控制面占住。 */
        val commandType:String?=null,
        /** 对端在响应头里回填的 CSeq；null 表示它没有回填。这决定能否按 CSeq 异步分发。 */
        val responseCseq:String?=null)
    @Volatile var onExchange:((Exchange)->Unit)?=null
    /** Fatal transport failure (including an idle EOF or request deadline).
     * Called once, never for local close. Must dispatch any blocking session cleanup. */
    @Volatile var onFailure:((Throwable)->Unit)?=null
    /** The socket owner supplies an abort that unblocks BOTH read and write without
     * acquiring writeLock/record locks. Configure before starting the reader. */
    @Volatile var abortTransport:(()->Unit)?=null
    var afterEventReply:((RtspMessage,Int,ByteArray)->Unit)?=null
    /** 写与等分离：writeLock 只覆盖“写一帧”，session 由 reader 与 send 共用。 */
    private val writeLock=Any()
    private val seq=java.util.concurrent.atomic.AtomicInteger(0)
    private fun nextId():Int{
        while(true){
            val cur=seq.get()
            val next=if(cur>=Int.MAX_VALUE-1)1 else cur+1
            if(seq.compareAndSet(cur,next))return next
        }
    }
    private var warnedMissingCseq=false
    /** 单向发送用过的 CSeq：它们的迟到响应要被丢弃，而不是当成别的请求的应答。
     *  只丢这些——对端完全不回填或填错号的响应仍按原规则接受（固件自己也只写不读）。 */
    private data class OneWay(val method:String,val path:String,val bodyBytes:Int,val commandType:String?,val beganNs:Long)
    private val oneWay=java.util.concurrent.ConcurrentHashMap<Int,OneWay>()
    private val oneWayOrder=java.util.concurrent.ConcurrentLinkedQueue<Int>()
    /** 异步模式：读线程 + 按 CSeq 唤醒等待者。必须读掉每一条响应，否则对端的发送缓冲会被堆满。 */
    private class Waiter{val slot=java.util.concurrent.LinkedBlockingQueue<Any>(1)}
    private val pending=java.util.concurrent.ConcurrentHashMap<Int,Waiter>()
    private val deadlines=java.util.concurrent.ScheduledThreadPoolExecutor(1,{task->
        Thread(task,"rtsp-deadline").apply{isDaemon=true}
    }).apply{
        removeOnCancelPolicy=true
        setExecuteExistingDelayedTasksAfterShutdownPolicy(false)
    }
    private val events=java.util.concurrent.LinkedBlockingQueue<RtspMessage>(64)
    @Volatile private var reader:Thread?=null
    @Volatile private var eventThread:Thread?=null
    @Volatile private var closed=false
    @Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
    private val lifecycleLock=java.lang.Object()
    private var activeOperations=0
    private var stopResult:java.util.concurrent.CompletableFuture<Unit>?=null
    @Volatile var sessionStopping=false;private set
    @Volatile private var terminalCause:Throwable?=null
    @Volatile var lastMessageNanos=0L;private set
    @Volatile var lastResponseNanos=0L;private set
    @Volatile var lastWriteNanos=0L;private set
    val readerRunning:Boolean get()=reader?.isAlive==true&&!closed
    /** Bounded, recent one-way requests without a correlated response; not blocking waiters. */
    val oneWayPendingCount:Int get()=oneWay.size
    private fun ensureOpen(){if(closed)throw IOException("RTSP client closed",terminalCause)}
    private inline fun <T> operation(block:()->T):T {
        synchronized(lifecycleLock){
            ensureOpen()
            if(sessionStopping)throw IOException("RTSP session stopping")
            activeOperations++
        }
        try{return block()}finally{synchronized(lifecycleLock){activeOperations--;lifecycleLock.notifyAll()}}
    }

    /** Whole-session stop for our non-connection-sharing profile (24A446 LC01/02).
     * Reject new business, drain already accepted operations, then send exactly one
     * empty dictionary (NOT streams:[]). Retain reader/transport until the owner
     * cleans up. The local total deadline covers drain, wire write and response;
     * abortTransport must unblock socket IO. This 5s UX bound is not Apple's 50s.
     * Repeated/concurrent callers observe the same result, never another request. */
    fun stopSession(path:String,budgetMs:Int=5_000){
        require(budgetMs>0)
        // The drain below waits for activeOperations to reach zero, and this thread may itself be
        // one of them (a failure observed on the control reader/event path). Waiting there would
        // stall until the budget expired and surface as InterruptedException, so refuse early: the
        // owner must call this from its own thread, and the caller's cleanup still closes the socket.
        require(Thread.currentThread()!==reader&&Thread.currentThread()!==eventThread){
            "Whole-session stop must not run on the control reader/event thread"
        }
        var owner=false
        val result=synchronized(lifecycleLock){
            stopResult?:run{
                ensureOpen();check(reader!=null){"No asynchronous session control"}
                sessionStopping=true;owner=true
                java.util.concurrent.CompletableFuture<Unit>().also{stopResult=it}
            }
        }
        if(owner){
            var deadline:java.util.concurrent.ScheduledFuture<*>?=null
            try{
                synchronized(lifecycleLock){
                    ensureOpen()
                    deadline=deadlines.schedule({
                        failAll(java.net.SocketTimeoutException("RTSP whole-session stop exceeded ${budgetMs}ms"),
                            "session-stop-deadline",expiredStop=result)
                    },budgetMs.toLong(),java.util.concurrent.TimeUnit.MILLISECONDS)
                    while(activeOperations>0&&!closed)lifecycleLock.wait()
                    ensureOpen()
                }
                val reply=requestInternal("TEARDOWN",path,Plist.encode(emptyMap<String,Any?>()))
                if(reply.status !in 200..299)throw StatusException(reply.status,"TEARDOWN",path)
                if(reply.body.isNotEmpty())Plist.dictionary(reply.body)
                // A peer may close immediately after its matching 2xx. That does
                // not undo a response already delivered to this transaction.
                synchronized(lifecycleLock){result.complete(Unit)}
            }catch(t:Throwable){
                synchronized(lifecycleLock){result.completeExceptionally(terminalCause?:t)}
            }finally{deadline?.cancel(false)}
        }
        try{result.get()}catch(t:java.util.concurrent.ExecutionException){throw requireNotNull(t.cause)}
    }
    /** Async request deadline, covering write-lock wait, socket write and reply.
     * Captured once per request; establishment may temporarily raise it. */
    @Volatile var timeoutMs:Int=10_000
    /** 还在等响应的请求数；心跳用它判断控制面是否被某条请求占住。 */
    val pendingCount:Int get()=pending.size
    @Volatile private var session:String?=null
    private var encryptedEpoch=false
    /** One constructor for sync, async and one-way requests. This declaration is
     * profile-owned: matching legacy extras coalesce case-insensitively, while a
     * conflicting value or an out-of-scope explicit declaration fails before write.
     * Other extra headers retain their existing case-sensitive override behavior. */
    private fun requestHeaders(id:Int,method:String,path:String,type:String,extra:Map<String,String>):Map<String,String> {
        val h=linkedMapOf("CSeq" to id.toString(),"User-Agent" to CarPlaySourceIdentity.userAgent,"Content-Type" to type)
        session?.let{h["Session"]=it}
        val version=CarPlayControlProfile.versionFor(method,path)
        extra.forEach{(name,value)->
            if(name.equals(CarPlayControlProfile.protocolVersionHeader,ignoreCase=true))
                require(version!=null&&value==version){"Protocol-version header conflicts with the local control profile"}
            else h[name]=value
        }
        version?.let{h[CarPlayControlProfile.protocolVersionHeader]=it}
        return h
    }
    /** 有读线程时走异步：写出去、在自己的 future 上等，别人的慢响应不占控制面。
     *  没有读线程时退回同步路径（加密流替换之前只能这样，swap 与常驻读者不能共存）。 */
    fun request(method:String,path:String,body:ByteArray=byteArrayOf(),type:String="application/x-apple-binary-plist",extra:Map<String,String> = emptyMap()):RtspMessage =
        operation{requestInternal(method,path,body,type,extra)}

    private fun requestInternal(method:String,path:String,body:ByteArray=byteArrayOf(),type:String="application/x-apple-binary-plist",extra:Map<String,String> = emptyMap()):RtspMessage {
        ensureOpen()
        if(reader==null)return requestSync(method,path,body,type,extra)
        val id=nextId()
        val began=System.nanoTime()
        val commandType=if(path=="/command"&&body.isNotEmpty())
            runCatching{Plist.dictionary(body)["type"] as? String}.getOrNull() else null
        var responseCseq:String?=null
        fun trace(phase:Phase,status:Int?=null,error:String?=null){
            runCatching{onExchange?.invoke(Exchange(phase,method,path,id,body.size,
                (System.nanoTime()-began)/1_000_000,status,error,0,commandType,responseCseq))}
        }
        trace(Phase.SEND)
        val waiter=Waiter()
        var deadline:java.util.concurrent.ScheduledFuture<*>?=null
        try{
            val budget=timeoutMs
            require(budget>0){"RTSP request deadline must be positive"}
            val h=requestHeaders(id,method,path,type,extra)
            synchronized(lifecycleLock){
                ensureOpen();pending[id]=waiter
                deadline=deadlines.schedule({
                    failAll(java.net.SocketTimeoutException("RTSP $method $path cseq=$id no response in ${budget}ms"),
                        "deadline",id,waiter)
                },budget.toLong(),java.util.concurrent.TimeUnit.MILLISECONDS)
            }
            synchronized(writeLock){ensureOpen();RtspWire.write(output,"$method $path ${"RTSP/1.0"}",h,body);lastWriteNanos=System.nanoTime()}
            val answer=waiter.slot.take()
            if(answer is Throwable)throw answer
            val r=answer as RtspMessage
            responseCseq=r.headers["cseq"]
            if(r.status==401)throw DigestRequired(r.headers["www-authenticate"])
            r.headers["session"]?.let{
                val received=it.substringBefore(';')
                require(received.isNotEmpty()&&received.length<=256&&received.none{ch->ch.isWhitespace()})
                require(session==null||session==received)
                if(r.status in 200..299)session=received
            }
            trace(Phase.RESPONSE,r.status)
            return r
        }catch(t:Exception){
            // A socket aborted by the deadline may throw during write first.
            // Preserve the initiating timeout, not the resulting "socket closed".
            val cause=terminalCause?:t
            trace(Phase.FAILED,error=cause.javaClass.simpleName);throw cause
        }finally{deadline?.cancel(false);pending.remove(id,waiter)}
    }
    private fun requestSync(method:String,path:String,body:ByteArray=byteArrayOf(),type:String="application/x-apple-binary-plist",extra:Map<String,String> = emptyMap()):RtspMessage {
        // 显式取锁而不是 @Synchronized：只有这样才能把“排队等锁”的时间和真正的往返分开。
        val entered=System.nanoTime()
        return synchronized<RtspMessage>(this){
        ensureOpen()
        val id=nextId()
        val began=System.nanoTime()
        val waited=(began-entered)/1_000_000
        val commandType=if(path=="/command"&&body.isNotEmpty())
            runCatching{Plist.dictionary(body)["type"] as? String}.getOrNull() else null
        var responseCseq:String?=null
        fun trace(phase:Phase,status:Int?=null,error:String?=null){
            runCatching{onExchange?.invoke(Exchange(phase,method,path,id,body.size,
                (System.nanoTime()-began)/1_000_000,status,error,waited,commandType,responseCseq))}
        }
        trace(Phase.SEND)
        try{
        val h=requestHeaders(id,method,path,type,extra)
        synchronized(writeLock){ensureOpen();RtspWire.write(output,"$method $path ${"RTSP/1.0"}",h,body);lastWriteNanos=System.nanoTime()}
        while(true) {
            val r=RtspWire.read(input,readProgress)
            lastMessageNanos=System.nanoTime()
            if(r.status==0){val (status,b)=event(r);reply(output,r,status,b);afterEventReply?.invoke(r,status,b);continue}
            lastResponseNanos=lastMessageNanos
            // 固件只写不读 CSeq，且它的响应方不回填；不能因为缺失或不一致就拒响应。
            val cseq=r.headers["cseq"]
            responseCseq=cseq
            // 这两种情况要分开：不匹配说明对端会回填但值不对，缺失说明它根本不回填——
            // 后者决定我们不能按 CSeq 异步分发响应。缺失只报一次，免得刷日志。
            if(cseq==null&&!warnedMissingCseq){
                warnedMissingCseq=true
                runCatching{onExchange?.invoke(Exchange(Phase.RESPONSE,method,path,id,body.size,
                    (System.nanoTime()-began)/1_000_000,r.status,"cseq-absent"))}
            }
            val numeric=cseq?.toIntOrNull()
            if(numeric!=null&&numeric!=id&&oneWay.remove(numeric)!=null){
                // 这是此前单向发送的迟到响应：丢掉，不能当成这次请求的应答。
                runCatching{onExchange?.invoke(Exchange(Phase.RESPONSE,method,path,id,body.size,
                    (System.nanoTime()-began)/1_000_000,r.status,"cseq-oneway:"+numeric))}
                continue
            }
            // A Digest challenge is terminal for this unsupported auth schema; it never
            // authorizes retrying the same peer through a weaker authentication path.
            if(r.status==401)throw DigestRequired(r.headers["www-authenticate"])
            r.headers["session"]?.let{
                val received=it.substringBefore(';')
                require(received.isNotEmpty()&&received.length<=256&&received.none{ch->ch.isWhitespace()})
                require(session==null||session==received)
                if(r.status in 200..299)session=received
            }
            trace(Phase.RESPONSE,r.status)
            return r
        }
        }catch(t:Exception){trace(Phase.FAILED,error=t.javaClass.simpleName);throw t}
        // 读循环只用非局部 return 退出；这句只为让 synchronized 块有确定的返回类型。
        @Suppress("UNREACHABLE_CODE") throw IllegalStateException("request loop exited")
        }
    }
    /** Explicit fire-and-forget only. Normal /feedback and iAPSendMessage use request.
     *  迟到的响应由下一次 [request] 的读循环按 CSeq 丢弃，不会错配到别的请求上；
     *  对端回得再慢也只影响它自己，占不住控制面。 */
    fun send(method:String,path:String,body:ByteArray=byteArrayOf(),
             type:String="application/x-apple-binary-plist",extra:Map<String,String> = emptyMap())=operation{
        ensureOpen()
        val id=nextId()
        val began=System.nanoTime()
        val commandType=if(path=="/command"&&body.isNotEmpty())
            runCatching{Plist.dictionary(body)["type"] as? String}.getOrNull() else null
        fun trace(phase:Phase,status:Int?=null,error:String?=null){
            runCatching{onExchange?.invoke(Exchange(phase,method,path,id,body.size,
                (System.nanoTime()-began)/1_000_000,status,error,0,commandType,null))}
        }
        trace(Phase.SEND)
        try{
            val h=requestHeaders(id,method,path,type,extra)
            synchronized(lifecycleLock){
                ensureOpen()
                oneWay[id]=OneWay(method,path,body.size,commandType,began)
                oneWayOrder.add(id)
                while(oneWayOrder.size>64){val oldest=oneWayOrder.poll()?:break;oneWay.remove(oldest)}
            }
            synchronized(writeLock){ensureOpen();RtspWire.write(output,"$method $path ${"RTSP/1.0"}",h,body);lastWriteNanos=System.nanoTime()}
        }catch(t:Exception){oneWay.remove(id);trace(Phase.FAILED,error=t.javaClass.simpleName);throw t}
    }
    /** 进入异步模式。必须在 [encrypted] 之后调用：换流与常驻读线程不能共存。
     *  之后每条响应都会被读掉——包括没人等的单向响应。不读的话，对端会把自己的发送缓冲
     *  堆满并卡在 write 上。是否发生于某次现场故障仍需对端或抓包证据。 */
    @Synchronized fun startReader(){
        check(!closed){"RTSP client closed"}
        if(reader!=null)return
        reader=Thread({
            try{
                while(!closed){
                    readProgress.reader("read")
                    val message=RtspWire.read(input,readProgress)
                    readProgress.reader("dispatch")
                    lastMessageNanos=System.nanoTime()
                    if(message.status==0){
                        if(!events.offer(message))runCatching{onExchange?.invoke(Exchange(Phase.FAILED,"event","",0,0,0,null,"event-queue-full"))}
                        continue
                    }
                    lastResponseNanos=lastMessageNanos
                    val cseq=message.headers["cseq"]?.toIntOrNull()
                    val delivered=synchronized(lifecycleLock){
                        val waiter=if(closed||cseq==null)null else pending.remove(cseq)
                        waiter?.slot?.offer(message)==true
                    }
                    if(!delivered){
                        val sent=if(cseq==null)null else oneWay.remove(cseq)
                        readProgress.reader("trace")
                        runCatching{onExchange?.invoke(if(sent!=null)
                            Exchange(Phase.RESPONSE,sent.method,sent.path,requireNotNull(cseq),sent.bodyBytes,
                                (System.nanoTime()-sent.beganNs)/1_000_000,message.status,
                                commandType=sent.commandType,responseCseq=cseq.toString())
                            else Exchange(Phase.RESPONSE,"?","?",cseq?:0,0,0,message.status,"unmatched:"+cseq))}
                    }
                }
                readProgress.reader("stopped")
            }catch(t:Throwable){readProgress.reader(if(closed)"stopped" else "failed");failAll(t)}
        },"rtsp-reader").apply{isDaemon=true;start()}
        eventThread=Thread({
            while(!closed){
                val message=try{events.poll(200,java.util.concurrent.TimeUnit.MILLISECONDS)}
                    catch(_:InterruptedException){break}?:continue
                try{
                    val (status,body)=event(message)
                    synchronized(writeLock){reply(output,message,status,body)}
                    afterEventReply?.invoke(message,status,body)
                }catch(t:Throwable){
                    runCatching{onExchange?.invoke(Exchange(Phase.FAILED,"event",message.first,0,0,0,null,t.javaClass.simpleName))}
                }
            }
        },"rtsp-events").apply{isDaemon=true;start()}
    }
    /** Invalidate only this connection. Late replies/timers cannot resurrect it. */
    internal fun invalidate(t:Throwable){failAll(t,"invalidate")}
    private fun failAll(t:Throwable,source:String="reader",expiredId:Int?=null,expiredWaiter:Waiter?=null,
                        expiredStop:java.util.concurrent.CompletableFuture<Unit>?=null){
        synchronized(lifecycleLock){
            if(closed)return
            // Response completion and deadline claim the same waiter under this lock.
            if(expiredId!=null&&pending[expiredId]!==expiredWaiter)return
            if(expiredStop!=null&&(stopResult!==expiredStop||expiredStop.isDone))return
            terminalCause=t;closed=true
            pending.values.forEach{it.slot.offer(t)}
            pending.clear();oneWay.clear();oneWayOrder.clear()
            lifecycleLock.notifyAll()
        }
        deadlines.shutdown()
        runCatching{abortTransport?.invoke()}
        reader?.interrupt()
        eventThread?.interrupt()
        runCatching{onExchange?.invoke(Exchange(Phase.FAILED,source,"",0,0,0,error=t.javaClass.simpleName))}
        runCatching{onFailure?.invoke(t)}
    }
    fun close(){
        synchronized(lifecycleLock){
            if(closed)return
            closed=true
            pending.values.forEach{it.slot.offer(IOException("RTSP client closed",terminalCause))}
            pending.clear();oneWay.clear();oneWayOrder.clear()
            lifecycleLock.notifyAll()
        }
        deadlines.shutdown()
        runCatching{abortTransport?.invoke()}
        reader?.interrupt()
        eventThread?.interrupt()
    }
    fun plist(method:String,path:String,value:Any?=emptyMap<String,Any?>()):Map<String,Any?> {
        val r=request(method,path,Plist.encode(value));if(r.status !in 200..299)throw StatusException(r.status,method,path)
        return if(r.body.isEmpty())emptyMap()else Plist.dictionary(r.body)
    }
    @Synchronized fun encrypted(shared:ByteArray) {
        require(shared.size==32);check(!encryptedEpoch)
        // 换流必须与“写一帧”互斥：send() 只拿 writeLock，不拿 this。
        // 完整性掩码在这里生效：通过时 pad 为空、apply 是恒等；失败时控制记录层密钥被污染。
        val key=shared
        val encryptedOutput=RecordOutput(output,Crypto.hkdf(key,"Control-Salt","Control-Write-Encryption-Key"))
        val encryptedInput=RecordInput(input,Crypto.hkdf(key,"Control-Salt","Control-Read-Encryption-Key")).also{it.diagnostics=readProgress}
        synchronized(writeLock){output=encryptedOutput;input=encryptedInput};encryptedEpoch=true
    }
    companion object {
        fun reply(out:OutputStream,r:RtspMessage,status:Int,b:ByteArray=byteArrayOf(),allowMissingCSeq:Boolean=false){
            val h=linkedMapOf<String,String>()
            val cseq=r.headers["cseq"]
            if(cseq!=null)h["CSeq"]=cseq
            else check(allowMissingCSeq){"Missing event CSeq"}
            // Dedicated event notifications may omit CSeq. Reply without inventing one;
            // control request/response correlation remains strict.
            if(b.isNotEmpty())h["Content-Type"]="application/x-apple-binary-plist"
            RtspWire.write(out,"${"RTSP/1.0"} $status "+if(status==200)"OK" else "Not Implemented",h,b)
        }
    }
}

/** 车机在某个端点上要求 HTTP Digest 应答。本实现不做 Digest 应答（规格只标了它的存在），
 *  所以这是一条"此端点走不通"的信号，而不是网络问题 —— 它必须是终局失败，否则会被无限重试。 */
class DigestRequired(val challenge:String?):java.io.IOException(
    "${"receiver requires HTTP Digest auth ("}"+(challenge?:"${"no WWW-Authenticate header"}")+"${"); this build does not implement a Digest response"}")
