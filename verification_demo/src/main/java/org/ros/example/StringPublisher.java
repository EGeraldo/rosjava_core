package org.ros.example;

import org.ros.namespace.GraphName;
import org.ros.node.topic.Publisher;
import org.ros.node.topic.PublisherListener;
import std_msgs.String;

import java.util.concurrent.TimeUnit;

public class StringPublisher implements  Publisher<std_msgs.String>{

    private Publisher<std_msgs.String> p;

    public StringPublisher(Publisher<std_msgs.String> p){
        this.p = p;
    }

    @Override
    public void setLatchMode(boolean enabled) {
        p.setLatchMode(enabled);
    }

    @Override
    public boolean getLatchMode() {
        return p.getLatchMode();
    }

    @Override
    public std_msgs.String newMessage() {
        return p.newMessage();
    }

    @Override
    public void publish(std_msgs.String message) {
        p.publish(message);
    }

    @Override
    public boolean hasSubscribers() {
        return p.hasSubscribers();
    }

    @Override
    public int getNumberOfSubscribers() {
        return p.getNumberOfSubscribers();
    }

    @Override
    public void shutdown(long timeout, TimeUnit unit) {
        p.shutdown(timeout, unit);
    }

    @Override
    public void shutdown() {
        p.shutdown();
    }

    @Override
    public void addListener(PublisherListener<String> listener) {
        p.addListener(listener);
    }

    @Override
    public GraphName getTopicName() {
        return p.getTopicName();
    }

    @Override
    public java.lang.String getTopicMessageType() {
        return p.getTopicMessageType();
    }
}
