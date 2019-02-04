
package org.ros.example.supervisor;

import org.apache.commons.logging.Log;
import org.ros.example.*;
import org.ros.namespace.GraphName;

import java.util.concurrent.locks.*;

/*@
predicate SupervCommonInv(VeriSupervisor self) =
	self.lck |-> ?lck &*& lck != null
 	&*& lck(lck, 1, SupervSS(self));

predicate SupervCreatedInv(VeriSupervisor self) =
 	self.pub |-> ?p &*& p==null
 	&*& self.log |-> ?l &*& l==null
 	&*& SupervCommonInv(self);

predicate SupervInitializedInv(VeriSupervisor self) =
 	self.pub |-> ?p &*& p!=null
 	&*& self.log |-> ?l &*& l!=null
 	&*& [_]SupervCommonInv(self);

predicate_ctor SupervSS(VeriSupervisor vs)() =
	vs.workers |-> ?w
	&*& w != null;

predicate Sensor_frac(real r) = true;
@*/

public class VeriSupervisor extends WrapperAbstractNodeMain {

    public IntegerQueue workers;
    public StringPublisher pub;
    public Log log;
    public ReentrantLock lck;

    public VeriSupervisor()
    //@ requires true;
    //@ ensures SupervCreatedInv(this);
    {
        this.workers = new IntegerLinkedList();
        //@ close SupervSS(this)();
        //@ close enter_lck(1, SupervSS(this));
        lck = new ReentrantLock();
        //@ close SupervCommonInv(this);
        //@ close SupervCreatedInv(this);
    }

    public GraphName getDefaultNodeName() {
        return GraphName.of("veriros/supervisor");
    }

    public void internalOnStart(WrapperConnectedNode connectedNode)
    /*@ 
    requires
    	SupervCreatedInv(this)
    	&*& connectedNode != null
    	&*& std_msgs.String._TYPE |-> ?f &*& f != null
    	&*& System.out |-> ?out &*& out != null;
    @*/
    //@ ensures SupervInitializedInv(this);
    {
        //@ open SupervCreatedInv(this);
        //@ open SupervCommonInv(this);

        log = connectedNode.getLog();

        pub = connectedNode.newPublisher("work", std_msgs.String._TYPE);

        StringSubscriber sub = connectedNode.newSubscriber("work_reply", std_msgs.String._TYPE);

        //@ close SupervCommonInv(this);
        //@ close SupervInitializedInv(this);
        sub.addMessageListener(new SupervisorMessageListener(this));

        SupervisorCancellableLoop scl = new SupervisorCancellableLoop(this);

        connectedNode.executeCancellableLoop(scl);
    }

}
