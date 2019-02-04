package org.ros.example;

import org.ros.message.MessageListener;
import org.ros.namespace.GraphName;
import org.ros.node.topic.Subscriber;
import org.ros.node.topic.SubscriberListener;
import std_msgs.String;

import java.util.concurrent.TimeUnit;

public class StringSubscriber implements Subscriber<String> {

    private Subscriber<String> s;

    public StringSubscriber(Subscriber<String> s) {
        this.s = s;
    }

    @Override
    public void addMessageListener(MessageListener<String> messageListener, int limit) {
        s.addMessageListener(messageListener, limit);
    }

    @Override
    public void addMessageListener(MessageListener<String> messageListener) {
        s.addMessageListener(messageListener);
    }

    public void addMessageListener(StringMessageListener messageListener) {
        s.addMessageListener(messageListener);
    }

    @Override
    public boolean removeMessageListener(MessageListener<String> messageListener) {
        return s.removeMessageListener(messageListener);
    }

    @Override
    public void removeAllMessageListeners() {
        s.removeAllMessageListeners();
    }

    @Override
    public void shutdown(long timeout, TimeUnit unit) {
        s.shutdown(timeout, unit);
    }

    @Override
    public void shutdown() {
        s.shutdown();
    }

    @Override
    public void addSubscriberListener(SubscriberListener<String> listener) {
        s.addSubscriberListener(listener);
    }

    @Override
    public boolean getLatchMode() {
        return s.getLatchMode();
    }

    @Override
    public GraphName getTopicName() {
        return s.getTopicName();
    }

    @Override
    public java.lang.String getTopicMessageType() {
        return s.getTopicMessageType();
    }
}
