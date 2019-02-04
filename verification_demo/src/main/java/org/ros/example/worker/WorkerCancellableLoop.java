package org.ros.example.worker;

import org.ros.concurrent.CancellableLoop;

/*@
predicate WorkerCLInv(WorkerCancellableLoop self) =
	self.vw |-> ?vwv &*& vwv!=null
	&*& WorkerInitializedInv(vwv)
	&*& self.finish |-> ?f;

predicate LoopInv(WorkerCancellableLoop self, VeriWorker worker) =
    self.vw |-> worker &*& worker != null &*& worker.pub |-> ?p &*& p != null
    &*& worker.log |-> ?l &*& l != null &*& worker.nodeId |-> ?id &*& id >= 0;

@*/

public class WorkerCancellableLoop extends CancellableLoop {

    private VeriWorker vw;
    private boolean finish;

    public WorkerCancellableLoop(VeriWorker vw)
    //@ requires vw != null &*& WorkerInitializedInv(vw);
    //@ ensures WorkerInitializedInv(vw);
    {
        this.vw = vw;
    }

    protected void loop() throws InterruptedException /*@ensures WorkerCLInv(this);@*/
    //@ requires WorkerCLInv(this);
    //@ ensures WorkerCLInv(this);
    {
        //@ open WorkerCLInv(this);
        if (finish) {
            //@ close WorkerCLInv(this);
            return;
        }

        //@ open WorkerInitializedInv(vw);
        //@ close LoopInv(this, ?val);
        for (int i = 0; i < 5; i++)
        //@ invariant i >= 0 &*& i <= 5 &*& LoopInv(this, val);
        {
            //@ open LoopInv(this, val);
            vw.log.info("Sending greeting");
            vw.pub.publish(buildGreeting());

            //@ close LoopInv(this, val);
            Thread.sleep(3000);
        }
        //@ open LoopInv(this, val);
        vw.log.info("Stopped Pinging");
        finish = true;

        //@ close WorkerInitializedInv(vw);
        //@ close WorkerCLInv(this);
    }

    public std_msgs.String buildGreeting()
    //@ requires this.vw |-> ?worker &*& worker.nodeId |-> ?id &*& id >= 0 &*& worker.pub |-> ?p &*& p != null;
    //@ ensures this.vw |-> worker &*& worker.nodeId |-> id &*& id >= 0 &*& worker.pub |-> p &*& p != null &*& result != null;
    {
        java.lang.String message = "Hello " + Integer.toString(vw.nodeId);

        return buildMessage(message);
    }

    private std_msgs.String buildMessage(java.lang.String message)
    //@ requires this.vw |-> ?worker &*& worker.pub |-> ?p &*& p != null &*& message != null;
    //@ ensures this.vw |-> worker &*& worker.pub |-> p &*& p != null &*& result != null;
    {
        std_msgs.String messageWrapper = vw.pub.newMessage();
        messageWrapper.setData(message);

        return messageWrapper;
    }

}
