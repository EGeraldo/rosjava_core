
package org.ros.example.worker;

import org.apache.commons.logging.Log;
import org.ros.example.*;
import org.ros.namespace.GraphName;
import org.ros.node.Node;

import java.util.Random;


/*@
predicate WorkerCreatedInv(VeriWorker self) =
	    self.nodeId |-> ?id &*& id >= 0
 	&*& self.pub    |-> ?p  &*& p == null
 	&*& self.log    |-> ?l  &*& l == null;

predicate WorkerInitializedInv(VeriWorker self) =
	    self.nodeId |-> ?id &*& id >= 0
 	&*& self.pub    |-> ?p  &*& p != null
 	&*& self.log    |-> ?l  &*& l != null;
 	
predicate WorkerTerminatedInv(VeriWorker self) =
	    self.nodeId |-> ?id &*& id < 0
 	&*& self.pub    |-> ?p  &*& p == null
 	&*& self.log    |-> ?l  &*& l == null;
@*/

public class VeriWorker extends WrapperAbstractNodeMain {

    public StringPublisher pub;
    public int nodeId;
    public Log log;


    public VeriWorker()
    //@ requires true;
    //@ ensures WorkerCreatedInv(this);
    {
        nodeId = new Random().nextInt(Integer.MAX_VALUE);
        //@ close WorkerCreatedInv(this);
    }

    public GraphName getDefaultNodeName() {
        return GraphName.of("veriros/worker" + nodeId);
    }

    public void internalOnStart(WrapperConnectedNode connectedNode)
    /*@
	requires WorkerCreatedInv(this) 
	     &*& connectedNode != null 
	     &*& std_msgs.String._TYPE |-> ?f &*& f != null 
	     &*& System.out |-> ?out &*& out != null;
    @*/
    //@ ensures WorkerInitializedInv(this);
    {
        //@ open WorkerCreatedInv(this);
        log = connectedNode.getLog();
        pub = connectedNode.newPublisher("work_reply", std_msgs.String._TYPE);

        StringSubscriber sub = connectedNode.newSubscriber("work", std_msgs.String._TYPE);
        sub.addMessageListener(new WorkerMessageListener(nodeId, log, pub));

        //@ close WorkerInitializedInv(this);
        std_msgs.String greeting = buildGreeting();

        WorkerCancellableLoop scl = new WorkerCancellableLoop(this);
        connectedNode.executeCancellableLoop(scl);
    }

    public void onShutdown(Node node)
    //@ requires WorkerInitializedInv(this);
    //@ ensures WorkerTerminatedInv(this);
    {
        std_msgs.String goodbye = buildGoodbye();

        //@ open WorkerInitializedInv(this);
        pub.publish(goodbye);

        nodeId = -1;
        pub = null;
        log = null;

        //@ close WorkerTerminatedInv(this);
    }

    public std_msgs.String buildGreeting()
    //@ requires WorkerInitializedInv(this);
    //@ ensures WorkerInitializedInv(this) &*& result != null;
    {
        //@ open WorkerInitializedInv(this);
        java.lang.String message = "Hello " + Integer.toString(nodeId);

        //@ close WorkerInitializedInv(this);
        return buildMessage(message);
    }

    private std_msgs.String buildGoodbye()
    //@ requires WorkerInitializedInv(this);
    //@ ensures WorkerInitializedInv(this) &*& result != null;
    {
        //@ open WorkerInitializedInv(this);
        java.lang.String message = "Bye " + Integer.toString(nodeId);

        //@ close WorkerInitializedInv(this);
        return buildMessage(message);
    }

    private std_msgs.String buildMessage(java.lang.String message)
    //@ requires message != null &*& WorkerInitializedInv(this);
    //@ ensures WorkerInitializedInv(this) &*& result != null;
    {
        //@ open WorkerInitializedInv(this);
        std_msgs.String messageWrapper = pub.newMessage();
        messageWrapper.setData(message);

        return messageWrapper;
        //@ close WorkerInitializedInv(this);
    }
}
