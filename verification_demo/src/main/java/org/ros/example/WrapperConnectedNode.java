package org.ros.example;

import org.apache.commons.logging.Log;
import org.ros.concurrent.CancellableLoop;
import org.ros.node.ConnectedNode;
import org.ros.node.topic.Publisher;
import org.ros.node.topic.Subscriber;

public class WrapperConnectedNode {

    private ConnectedNode cn;

    public WrapperConnectedNode(ConnectedNode cn) {
        this.cn = cn;
    }

    public final Log getLog() {
        return cn.getLog();
    }

    public StringPublisher newPublisher(java.lang.String topicName, java.lang.String messageType) {
        Publisher<std_msgs.String> p = cn.newPublisher(topicName, messageType);

        return new StringPublisher(p);
    }

    public StringSubscriber newSubscriber(java.lang.String topicName, java.lang.String messageType) {
        Subscriber<std_msgs.String> s = cn.newSubscriber(topicName, messageType);

        return new StringSubscriber(s);
    }

    public void executeCancellableLoop(CancellableLoop cancellableLoop) {
        cn.executeCancellableLoop(cancellableLoop);
    }
}
