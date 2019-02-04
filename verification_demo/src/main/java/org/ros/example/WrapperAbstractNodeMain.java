package org.ros.example;

import org.ros.node.AbstractNodeMain;
import org.ros.node.ConnectedNode;

public abstract class WrapperAbstractNodeMain extends AbstractNodeMain {

    @Override
    public final void onStart(ConnectedNode connectedNode) {
        internalOnStart(new WrapperConnectedNode(connectedNode));
    }

    public abstract void internalOnStart(WrapperConnectedNode connectedNode);
}
