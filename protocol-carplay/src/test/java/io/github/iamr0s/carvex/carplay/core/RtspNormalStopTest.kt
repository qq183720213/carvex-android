package io.github.iamr0s.carvex.carplay.core

import org.junit.Assert.*
import org.junit.Test
import java.io.*
import java.net.SocketTimeoutException
import java.util.concurrent.*

class RtspNormalStopTest {
    private val path="rtsp://192.0.2.1/123"
    private class Incoming:InputStream(){
        private val bytes=LinkedBlockingQueue<Int>()
        override fun read():Int=bytes.take()
        fun reply(id:Int,status:Int=200){
            "RTSP/1.0 $status Synthetic\r\nCSeq: $id\r\nSession: example\r\nContent-Length: 0\r\n\r\n"
                .toByteArray().forEach{bytes.put(it.toInt() and 255)}
        }
        override fun close(){bytes.offer(-1)}
    }
    private class Peer:AutoCloseable {
        val input=Incoming()
        val requests=LinkedBlockingQueue<RtspMessage>()
        val output=object:ByteArrayOutputStream(){
            override fun flush(){requests.put(RtspWire.read(ByteArrayInputStream(toByteArray())));reset()}
        }
        val client=RtspClient(input,output).apply{abortTransport={input.close()};startReader()}
        fun next():RtspMessage=requireNotNull(requests.poll(2,TimeUnit.SECONDS)){"No request"}
        fun reply(request:RtspMessage,status:Int=200)=input.reply(requireNotNull(request.headers["cseq"]).toInt(),status)
        override fun close(){client.close();input.close()}
    }
    private fun <T> task(block:()->T)=FutureTask(Callable(block)).also{Thread(it).apply{isDaemon=true;start()}}
    private fun awaitStopping(client:RtspClient){
        val until=System.nanoTime()+TimeUnit.SECONDS.toNanos(2)
        while(!client.sessionStopping&&System.nanoTime()<until)Thread.yield()
        assertTrue(client.sessionStopping)
    }

    @Test fun fullStopUsesCurrentSessionAndEmptyDictionaryThenKeepsReaderUntilOwnerCleanup(){
        Peer().use{p->
            val setup=task{p.client.request("SETUP",path)}
            p.reply(p.next());setup.get(2,TimeUnit.SECONDS)
            val stop=task{p.client.stopSession(path)}
            val request=p.next()
            assertEquals("TEARDOWN $path RTSP/1.0",request.first)
            assertEquals("example",request.headers["session"])
            assertEquals("2",request.headers["cseq"])
            assertTrue(Plist.dictionary(request.body).isEmpty()) // Neither streams nor teardownType.
            assertTrue(p.client.readerRunning);assertFalse(stop.isDone)
            p.reply(request);stop.get(2,TimeUnit.SECONDS)
            assertTrue(p.client.readerRunning)
            p.client.stopSession(path)
            assertTrue(p.requests.isEmpty())
            assertThrows(IOException::class.java){p.client.plist("SETUP",path)}
            assertThrows(IOException::class.java){p.client.send("POST","/feedback")}
        }
    }

    @Test fun acceptedPartialCloseDrainsBeforeFullStopAndNewBusinessIsRejected(){
        Peer().use{p->
            val partial=task{p.client.plist("TEARDOWN",path,mapOf("streams" to listOf(mapOf("type" to 101))))}
            val first=p.next()
            val stop=task{p.client.stopSession(path)}
            awaitStopping(p.client)
            assertThrows(IOException::class.java){p.client.plist("POST","/command")}
            assertThrows(IOException::class.java){p.client.plist("TEARDOWN",path,mapOf("streams" to emptyList<Any>()))}
            assertTrue(p.requests.isEmpty())
            p.reply(first);partial.get(2,TimeUnit.SECONDS)
            val full=p.next();assertTrue(Plist.dictionary(full.body).isEmpty())
            p.reply(full);stop.get(2,TimeUnit.SECONDS)
            assertTrue(p.requests.isEmpty())
        }
    }

    @Test fun concurrentStopsShareOneTransaction(){
        Peer().use{p->
            val first=task{p.client.stopSession(path)}
            val request=p.next()
            val second=task{p.client.stopSession(path)}
            assertFalse(first.isDone)
            p.reply(request);first.get(2,TimeUnit.SECONDS);second.get(2,TimeUnit.SECONDS)
            assertTrue(p.requests.isEmpty())
        }
    }

    @Test fun deliveredButStillBeingProcessedReplyIsNotMistakenForADrainedRequest(){
        Peer().use{p->
            val processing=CountDownLatch(1);val release=CountDownLatch(1)
            p.client.onExchange={e->if(e.method=="SETUP"&&e.phase==RtspClient.Phase.RESPONSE){
                processing.countDown();check(release.await(3,TimeUnit.SECONDS))
            }}
            try{
                val setup=task{p.client.request("SETUP",path)}
                p.reply(p.next());assertTrue(processing.await(2,TimeUnit.SECONDS))
                assertEquals(0,p.client.pendingCount)
                val stop=task{p.client.stopSession(path)}
                awaitStopping(p.client);assertTrue(p.requests.isEmpty())
                release.countDown();setup.get(2,TimeUnit.SECONDS)
                p.reply(p.next());stop.get(2,TimeUnit.SECONDS)
            }finally{release.countDown()}
        }
    }

    @Test fun responseAlreadyDeliveredRemainsAcceptedIfPeerThenCloses(){
        Peer().use{p->
            p.client.onExchange={e->if(e.method=="TEARDOWN"&&e.phase==RtspClient.Phase.RESPONSE)p.client.close()}
            val stop=task{p.client.stopSession(path)}
            p.reply(p.next());stop.get(2,TimeUnit.SECONDS)
            assertFalse(p.client.readerRunning)
        }
    }

    @Test fun normalCleanupCannotCloseControlBeforeConfirmationAndDoesNotLeakIntoNextConnection()=kotlinx.coroutines.runBlocking {
        Peer().use{p->
            val termination=io.github.iamr0s.carvex.sessioncore.SessionTermination{p.close()}
            assertTrue(termination.beginNormalStop())
            val stop=task{p.client.stopSession(path)}
            val request=p.next()
            termination.close() // A failure callback or attempt finally racing normal stop.
            assertTrue(p.client.readerRunning)
            p.reply(request);stop.get(2,TimeUnit.SECONDS)
            termination.finishNormalStop();termination.awaitClosed()
            assertFalse(p.client.readerRunning)
            Peer().use{next->
                val setup=task{next.client.request("SETUP",path)}
                val fresh=next.next();assertEquals("1",fresh.headers["cseq"])
                next.reply(fresh);setup.get(2,TimeUnit.SECONDS)
            }
        }
        Unit
    }

    @Test fun timeoutWhileDrainingAbortsTransportWithoutSendingFullStop(){
        Peer().use{p->
            val active=task{p.client.request("SETUP",path)}
            p.next()
            assertThrows(SocketTimeoutException::class.java){p.client.stopSession(path,120)}
            assertFalse(p.client.readerRunning)
            assertThrows(ExecutionException::class.java){active.get(2,TimeUnit.SECONDS)}
            assertTrue(p.requests.isEmpty())
        }
    }

    @Test fun silentOrUnrelatedReplyCannotConfirmStop(){
        for(unrelated in listOf(false,true))Peer().use{p->
            val stop=task{p.client.stopSession(path,120)}
            p.next();if(unrelated)p.input.reply(999)
            val failure=assertThrows(ExecutionException::class.java){stop.get(2,TimeUnit.SECONDS)}
            assertTrue(failure.cause is SocketTimeoutException)
            assertFalse(p.client.readerRunning)
            assertThrows(SocketTimeoutException::class.java){p.client.stopSession(path)}
            assertTrue(p.requests.isEmpty())
        }
    }

    @Test fun rejectionIsReportedAndNotRetried(){
        Peer().use{p->
            val stop=task{p.client.stopSession(path)}
            p.reply(p.next(),500)
            val error=assertThrows(ExecutionException::class.java){stop.get(2,TimeUnit.SECONDS)}
            assertTrue(error.cause is RtspClient.StatusException)
            assertThrows(RtspClient.StatusException::class.java){p.client.stopSession(path)}
            assertTrue(p.requests.isEmpty())
        }
    }

    @Test fun totalDeadlineAlsoUnblocksAnExistingSocketWrite(){
        val input=Incoming();val entered=CountDownLatch(1);val aborted=CountDownLatch(1)
        val output=object:OutputStream(){override fun write(value:Int){entered.countDown();check(aborted.await(3,TimeUnit.SECONDS));throw IOException("aborted")}}
        val client=RtspClient(input,output).apply{abortTransport={aborted.countDown();input.close()};startReader()}
        try{
            val active=task{client.request("SETUP",path)}
            assertTrue(entered.await(2,TimeUnit.SECONDS))
            assertThrows(SocketTimeoutException::class.java){client.stopSession(path,120)}
            assertThrows(ExecutionException::class.java){active.get(2,TimeUnit.SECONDS)}
            assertEquals(0L,aborted.count)
        }finally{client.close();input.close();aborted.countDown()}
    }

    @Test fun totalDeadlineAlsoUnblocksTheTeardownSocketWrite(){
        val input=Incoming();val aborted=CountDownLatch(1)
        val output=object:OutputStream(){override fun write(value:Int){check(aborted.await(3,TimeUnit.SECONDS));throw IOException("aborted")}}
        val client=RtspClient(input,output).apply{abortTransport={aborted.countDown();input.close()};startReader()}
        try{
            val stop=task{client.stopSession(path,120)}
            assertTrue(assertThrows(ExecutionException::class.java){stop.get(2,TimeUnit.SECONDS)}.cause is SocketTimeoutException)
            assertEquals(0L,aborted.count)
        }finally{client.close();input.close();aborted.countDown()}
    }

    @Test fun forcedCloseUnblocksNormalStop(){
        Peer().use{p->
            val stop=task{p.client.stopSession(path)}
            p.next();p.client.close()
            assertTrue(assertThrows(ExecutionException::class.java){stop.get(2,TimeUnit.SECONDS)}.cause is IOException)
        }
    }

    @Test fun pairingModeCannotSendAFullSessionStop(){
        val output=ByteArrayOutputStream()
        val client=RtspClient(ByteArrayInputStream(byteArrayOf()),output)
        try{assertThrows(IllegalStateException::class.java){client.stopSession(path)};assertEquals(0,output.size())}
        finally{client.close()}
    }

    @Test fun wholeSessionStopRefusesToRunOnTheControlReaderOrEventThread(){
        // Cleanup is reachable from the reader/event threads. Draining activeOperations there would
        // wait on the very operation that is calling in, so it is refused up front instead of
        // stalling until the budget expires.
        Peer().use{p->
            var readerFailure:Throwable?=null;var eventFailure:Throwable?=null
            val readerThread=Thread({readerFailure=runCatching{p.client.stopSession(path)}.exceptionOrNull()},
                "rtsp-reader")
            val eventThread=Thread({eventFailure=runCatching{p.client.stopSession(path)}.exceptionOrNull()},
                "rtsp-events")
            // The guard compares against the client's own threads, so emulate by direct field access
            // through reflection of the same names the client uses.
            val readerField=RtspClient::class.java.getDeclaredField("reader").apply{isAccessible=true}
            val eventField=RtspClient::class.java.getDeclaredField("eventThread").apply{isAccessible=true}
            val originalReader=readerField.get(p.client) as Thread?
            val originalEvent=eventField.get(p.client) as Thread?
            try{
                readerField.set(p.client,readerThread);readerThread.start();readerThread.join(2_000)
                assertTrue("stop on reader thread must be refused",readerFailure is IllegalArgumentException)
                eventField.set(p.client,eventThread);eventThread.start();eventThread.join(2_000)
                assertTrue("stop on event thread must be refused",eventFailure is IllegalArgumentException)
                // Nothing may have reached the wire while those callers were rejected.
                assertNull(p.requests.poll(200,TimeUnit.MILLISECONDS))
                assertFalse(p.client.sessionStopping)
            }finally{readerField.set(p.client,originalReader);eventField.set(p.client,originalEvent)}
        }
    }

    @Test fun repeatedWholeSessionStopSendsOneTeardown(){
        Peer().use{p->
            val first=task{p.client.stopSession(path)}
            val request=p.next()
            assertEquals("TEARDOWN $path RTSP/1.0",request.first)
            val second=task{p.client.stopSession(path)}
            p.reply(request)
            first.get(2,TimeUnit.SECONDS);second.get(2,TimeUnit.SECONDS)
            assertTrue("the repeated stop must not send a second request",
                p.requests.poll(300,TimeUnit.MILLISECONDS)==null)
        }
    }
}
