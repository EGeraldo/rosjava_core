package org.ros.example.supervisor;

import org.ros.example.StringMessageListener;

/*@
predicate SupervMLInv(SupervisorMessageListener self) =
	self.vs |-> ?vs &*& vs!=null
	&*& SupervInitializedInv(vs);

predicate TokenAccess(java.lang.String[] arr, int n) =
	arr != null
	&*& n > 0
	&*& arr.length == n
	&*& array_slice(arr, 0, arr.length, _);
@*/

public class SupervisorMessageListener implements StringMessageListener {

    private VeriSupervisor vs;

    public SupervisorMessageListener(VeriSupervisor vs)
    //@ requires vs != null &*& SupervInitializedInv(vs);
    //@ ensures SupervInitializedInv(vs);
    {
        this.vs = vs;
    }

    public void onNewMessage(std_msgs.String message)
    //@ requires SupervMLInv(this) &*& message != null;
    //@ ensures SupervMLInv(this);
    {
        processMessage(message.getData());
    }

    private void processMessage(java.lang.String message)
    //@ requires SupervMLInv(this) &*& message != null;
    //@ ensures SupervMLInv(this);
    {
        if (message.startsWith("Hello")) {
            processHello(message);
        } else if (message.startsWith("Work")) {
            processWorkComplete(message);
        } else if (message.startsWith("Bye")) {
            processBye(message);
        } else {
            //@ open SupervMLInv(this);
            //@ open SupervInitializedInv(vs);
            vs.log.info("Unknown message type received");
            //@ close SupervInitializedInv(vs);
            //@ close SupervMLInv(this);
        }
    }

    private void processHello(java.lang.String hello)
    //@ requires SupervMLInv(this) &*& hello != null;
    //@ ensures SupervMLInv(this);
    {
        //@ open SupervMLInv(this);
        //@ open SupervInitializedInv(vs);
        vs.log.info("Hello: <" + hello + ">");
        //@ close SupervInitializedInv(vs);
        //@ close SupervMLInv(this);

        java.lang.String[] tokens = validateAndTokenizeHello(hello);

        if (tokens == null)
            return;

        addWorker(tokens, 1);
    }

    private void processWorkComplete(java.lang.String wc)
    //@ requires SupervMLInv(this) &*& wc != null;
    //@ ensures SupervMLInv(this);
    {
        //@ open SupervMLInv(this);
        //@ open SupervInitializedInv(vs);
        vs.log.info("Worker finished: <" + wc + ">");
        //@ close SupervInitializedInv(vs);
        //@ close SupervMLInv(this);

        java.lang.String[] tokens = validateAndTokenizeWorkComplete(wc);

        if (tokens == null)
            return;

        addWorker(tokens, 1);
    }

    private void processBye(java.lang.String bye)
    //@ requires SupervMLInv(this) &*& bye != null;
    //@ ensures SupervMLInv(this);
    {
        //@ open SupervMLInv(this);
        //@ open SupervInitializedInv(vs);
        vs.log.info("Bye: <" + bye + ">");
        //@ close SupervInitializedInv(vs);
        //@ close SupervMLInv(this);

        java.lang.String[] tokens = validateAndTokenizeBye(bye);

        if (tokens == null)
            return;

        remWorker(tokens, 1);
    }

    private java.lang.String[] validateAndTokenizeHello(java.lang.String hello)
    //@ requires hello != null;
    //@ ensures result != null ? TokenAccess(result, 2) : result == null;
    {
        java.lang.String[] tokens = hello.split(" ");
        if (tokens.length != 2)
            return null;
        //@ close TokenAccess(tokens, 2);
        return tokens;
    }

    private java.lang.String[] validateAndTokenizeWorkComplete(java.lang.String wc)
    //@ requires wc != null;
    //@ ensures result != null ? TokenAccess(result, 5) : result == null;
    {
        java.lang.String[] tokens = wc.split(" ");
        if (tokens.length != 5)
            return null;
        //@ close TokenAccess(tokens, 5);
        return tokens;
    }

    private java.lang.String[] validateAndTokenizeBye(java.lang.String bye)
    //@ requires bye != null;
    //@ ensures result != null ? TokenAccess(result, 2) : result == null;
    {
        java.lang.String[] tokens = bye.split(" ");
        if (tokens.length != 2)
            return null;
        //@ close TokenAccess(tokens, 2);
        return tokens;
    }

    private int validateAndRetrieveIdToken(java.lang.String[] tokens, int idx)
    //@ requires SupervMLInv(this) &*& TokenAccess(tokens, ?sz) &*& idx >= 0 &*& idx < sz;
    //@ ensures SupervMLInv(this);
    {
        //@ open TokenAccess(tokens, _);
        if (tokens[idx] == null)
            return -1;

        return Integer.parseInt(tokens[idx]);
    }

    private void addWorker(java.lang.String[] tokens, int idx)
    //@ requires SupervMLInv(this) &*& TokenAccess(tokens, ?sz) &*& idx >= 0 &*& idx < sz;
    //@ ensures SupervMLInv(this);
    {

        int id = validateAndRetrieveIdToken(tokens, idx);

        if (!isValidId(id))
            return;

        //@ open SupervMLInv(this);
        //@ open SupervInitializedInv(vs);
        //@ open [?f]SupervCommonInv(vs);
        vs.lck.lock();
        //@ open SupervSS(vs)();
        vs.workers.add(id);
        //@ close SupervSS(vs)();
        vs.lck.unlock();
        //@ close [f]SupervCommonInv(vs);
        //@ close SupervInitializedInv(vs);
        //@ close SupervMLInv(this);
    }

    private void remWorker(java.lang.String[] tokens, int idx)
    //@ requires SupervMLInv(this) &*& TokenAccess(tokens, ?sz) &*& idx >= 0 &*& idx < sz;
    //@ ensures SupervMLInv(this);
    {

        int id = validateAndRetrieveIdToken(tokens, idx);

        if (!isValidId(id))
            return;

        //@ open SupervMLInv(this);
        //@ open SupervInitializedInv(vs);
        //@ open [?f]SupervCommonInv(vs);
        vs.lck.lock();
        //@ open SupervSS(vs)();
        vs.workers.remove(id);
        //@ close SupervSS(vs)();
        vs.lck.unlock();
        //@ close [f]SupervCommonInv(vs);
        //@ close SupervInitializedInv(vs);
        //@ close SupervMLInv(this);
    }

    private boolean isValidId(int id)
    //@ requires true;
    //@ ensures result ? id >= 0 : id < 0;
    {
        return id >= 0;
    }
}
