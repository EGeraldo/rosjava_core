package org.ros.example.supervisor;

import org.ros.concurrent.CancellableLoop;

import java.util.Random;

/*@
predicate SupervCLInv(SupervisorCancellableLoop self) =
	self.vs |-> ?vsf &*& vsf!=null
	&*& SupervInitializedInv(vsf);

predicate LoopInv(SupervisorCancellableLoop self, VeriSupervisor sup) =
    self.vs |-> sup &*& sup != null &*& sup.workers |-> ?w &*& w != null &*& sup.pub |-> ?p &*& p != null
    &*& sup.log |-> ?l &*& l != null;

@*/

public class SupervisorCancellableLoop extends CancellableLoop {

    private VeriSupervisor vs;

    public SupervisorCancellableLoop(VeriSupervisor vs)
    //@ requires vs != null &*& SupervInitializedInv(vs);
    //@ ensures SupervInitializedInv(vs);
    {
        this.vs = vs;
    }


    protected void loop()
    //@ requires SupervCLInv(this);
    //@ ensures SupervCLInv(this);
    {
        //@ open SupervCLInv(this);
        //@ open SupervInitializedInv(vs);
        //@ open [?f]SupervCommonInv(vs);
        vs.lck.lock();
        //@ open SupervSS(vs)();

        int sz = vs.workers.size();

        //@ close LoopInv(this, ?vsf);
        for (int i = 0; i < sz; i++)
        //@ invariant LoopInv(this, vsf);
        {
            //@ open LoopInv(this, vsf);
            int workerId = vs.workers.remove();

            if (workerId < 0) {
                //@ close LoopInv(this, vsf);
                break;
            }

            std_msgs.String workReq = buildWorkRequest(workerId);
            vs.log.info("Sending work request: " + workReq.getData());
            vs.pub.publish(workReq);
            //@ close LoopInv(this, vsf);
        }
        //@ open LoopInv(this, vsf);

        //@ close SupervSS(vs)();
        vs.lck.unlock();
        //@ close [f]SupervCommonInv(vs);
        //@ close SupervInitializedInv(vs);
        //@ close SupervCLInv(this);
    }

    private std_msgs.String buildWorkRequest(int workerId)
    //@ requires this.vs |-> ?v &*& v.pub |-> ?p &*& p != null &*& workerId >= 0;
    //@ ensures this.vs |-> v &*& v.pub |-> p &*& p != null &*& result != null;
    {
        Random r = new Random();
        int bound0 = r.nextInt(1000);
        int bound1 = r.nextInt(1000);

        java.lang.String request =
                "Work " + Integer.toString(workerId) + " "
                        + Integer.toString(Math.min(bound0, bound1)) + " "
                        + Integer.toString(Math.max(bound0, bound1));

        std_msgs.String requestWrapper = vs.pub.newMessage();

        requestWrapper.setData(request);

        return requestWrapper;
    }

}
