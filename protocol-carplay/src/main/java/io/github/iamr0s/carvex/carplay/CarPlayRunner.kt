package io.github.iamr0s.carvex.carplay

import android.content.Context
import io.github.iamr0s.carvex.carplay.core.IapFields
import io.github.iamr0s.carvex.carplay.core.IapLink
import io.github.iamr0s.carvex.sessioncore.Options
import io.github.iamr0s.carvex.carplay.core.PairIdentity
import io.github.iamr0s.carvex.sessioncore.Resources
import io.github.iamr0s.carvex.carplay.core.RuntimeIapState
import io.github.iamr0s.carvex.carplay.core.SecurityBinding
import io.github.iamr0s.carvex.carplay.core.TouchSample

/**
 * CarPlay 会话的构造器（A 方案）。
 *
 * 职责限定为「把 Bootstrap 的握手调用与 AirSession 的构造收进协议模块」：
 * 链路的创建、握手后的 handoff/poll 仍留在编排层（那是传输与策略）。
 * 这样 `SessionController` 不再直接 `new AirSession`，也不再直接调 `Bootstrap.*`；
 * `air.xxx` 的媒体调用保持不变，行为与改造前逐字等价。
 *
 * 将来做 B 方案（协议驱动编排）时，把这个类升级成 `ProtocolRunner` 的实现即可。
 */
interface CarPlayHost {
    fun log(message: String)
    fun touch(sample: TouchSample): Boolean
    fun key(prefix: String, usage: Int, down: Boolean): Boolean
    fun failure(cause: Throwable)
    fun runtimeChanged(state: RuntimeIapState)
    fun ui(url: String): Boolean
    fun nightMode(mode: Int)
    fun focusOffer()
    fun voice(action: String): Boolean
    fun warn(message: String)
}

class CarPlayRunner(
    private val context: Context,
    private val options: Options,
    private val resources: Resources,
    private val host: CarPlayHost,
) {
    /** 建立蓝牙 RFCOMM 连接（链路层，握手前）。 */
    suspend fun openBluetooth(): android.bluetooth.BluetoothSocket =
        Bootstrap.bluetooth(context, options, resources, host::log)

    /** iAP2 握手（识别/认证/无线交接）；返回协商后的 Wi-Fi 启动信息。 */
    suspend fun negotiate(
        link: IapLink,
        phoneMac: String,
        deviceName: String,
        identity: PairIdentity,
        previous: WifiBootstrap?,
        experimentalIntegrityOnly: Boolean,
        onNowPlayingCommand: ((Int, IapFields) -> Boolean)? = null,
        onDigitalKeyRequest: DigitalKeyMatcher? = null,
        onDeviceWifiInfoRequest: DeviceWifiInfoProvider? = null,
        onCarPlayStartRequest: CarPlayStartRequest? = null,
        onWifiAnnouncement: WifiAnnouncementHandler? = null,
        networkHandoff: IapNetworkHandoff? = null,
    ): WifiBootstrap = Bootstrap.negotiate(
        link, phoneMac, deviceName, identity, previous,
        experimentalIntegrityOnly = experimentalIntegrityOnly,
        log = host::log,
        onNowPlayingCommand = onNowPlayingCommand,
        onDigitalKeyRequest = onDigitalKeyRequest,
        onDeviceWifiInfoRequest = onDeviceWifiInfoRequest,
        onCarPlayStartRequest = onCarPlayStartRequest,
        onWifiAnnouncement = onWifiAnnouncement,
        networkHandoff = networkHandoff,
    )

    /** 加入车机 Wi-Fi 并准备网络路径。 */
    suspend fun openNetwork(bootstrap: WifiBootstrap, onFailure: (Throwable) -> Unit): NetworkPath =
        Bootstrap.network(context, bootstrap, resources, host::log, onFailure)

    suspend fun prepareNetwork(bootstrap:WifiBootstrap,handoff:IapNetworkHandoff,
        join:suspend(WifiBootstrap)->NetworkPath):NetworkHandoffPipeline.Ready<NetworkPath,CarPlayControlPublication> {
        val pipeline=NetworkHandoffPipeline(handoff,join,
            publish={path:NetworkPath->
                resources.own(CarPlayControlPublication(context,path,options,
                    {runCatching{handoff.requireCurrent()}.isSuccess},host::log,host::failure)).also{publication->
                    handoff.configuration()?.endpoint?.addresses.orEmpty().mapNotNull{address->
                        runCatching{Bootstrap.address(path.properties,address)}.getOrNull()
                    }.let(publication::candidates)
                    publication.start()
                }
            },
            discover={path,value->
                val discovery=ReceiverDiscovery(context,path,value,resources,host::log)
                try{
                    discovery.start()
                    val metadata=discovery.await()
                    value.resolved(requireNotNull(metadata.endpoint?.hostAddress),requireNotNull(metadata.port),
                        requireNotNull(metadata.deviceId),metadata.publicKey,metadata)
                }finally{resources.release(discovery)}
            })
        return pipeline.open(bootstrap)
    }

    /** 构造 AirSession；媒体管线仍由编排层通过返回对象驱动（A 方案）。
     *  `localFps` 与 `sourceContextCurrent` 依赖编排层状态，因此作为参数传入而不是放进 host。
     *
     *  The session is registered with `resources` so that every exit path closes it. Its own
     *  close() sends the whole-session TEARDOWN; without it a receiver keeps waiting on a session
     *  we already abandoned and never returns to its idle screen. */
    fun openSession(
        path: NetworkPath,
        bootstrap: WifiBootstrap,
        security: SecurityBinding,
        localFps: (Int, Int, Int) -> Int?,
        sourceContextCurrent: () -> Boolean,
        controlPublication: CarPlayControlPublication? = null,
    ): AirSession = resources.own(AirSession(
        context, path, bootstrap, options, resources,
        host::log,
        host::touch,
        host::key,
        host::failure,
        host::runtimeChanged,
        host::ui,
        host::nightMode,
        host::focusOffer,
        host::voice,
        host::warn,
        localFps,
        security,
        sourceContextCurrent,
        controlPublication = controlPublication,
    ))
}
