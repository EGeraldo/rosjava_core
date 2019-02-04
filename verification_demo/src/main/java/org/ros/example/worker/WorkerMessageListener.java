package org.ros.example.worker;

import org.apache.commons.logging.Log;
import org.ros.example.StringMessageListener;
import org.ros.example.StringPublisher;

/*@
predicate WorkerCommonInv(WorkerMessageListener self) =
	self.nodeId |-> ?id &*& id >= 0
 	&*& self.pub |-> ?p &*& p!=null
 	&*& self.log |-> ?l &*& l!=null;

predicate WorkerIdleInv(WorkerMessageListener self) =
	WorkerCommonInv(self)
 	&*& self.request |-> ?r &*& r == null;
 	
predicate WorkerRunningInv(WorkerMessageListener self) =
	WorkerCommonInv(self)
	&*& self.request |-> ?r &*& ValidRequest(r);
	//	&*& self.request |-> ?r &*& r != null &*& r.length == 4 &*& array_slice(r, 0, 4, _);

predicate ValidRequest(java.lang.String[] req) =
	req.length == 4 &*& array_slice(req, 0, 4, _);
 @*/

public class WorkerMessageListener implements StringMessageListener {

    private int nodeId;
    private Log log;
    private java.lang.String[] request;
    private StringPublisher pub;

    public WorkerMessageListener(int nodeId, Log log, StringPublisher pub)
    //@ requires nodeId >= 0 &*& log!=null &*& pub!=null;
    //@ ensures WorkerIdleInv(this);
    {
        this.nodeId = nodeId;
        this.log = log;
        this.pub = pub;

        //@ close WorkerCommonInv(this);
        //@ close WorkerIdleInv(this);
    }

    public void onNewMessage(std_msgs.String message)
    //@ requires WorkerIdleInv(this) &*& message != null;
    //@ ensures WorkerIdleInv(this);
    {
        //@ open WorkerIdleInv(this);
        //@ open WorkerCommonInv(this);
        log.info(message.getData());

        //@ close WorkerCommonInv(this);
        //@ close WorkerIdleInv(this);
        processMessage(message.getData());
    }

    private void processMessage(java.lang.String message)
    //@ requires WorkerIdleInv(this) &*& message != null;
    //@ ensures  WorkerIdleInv(this);
    {
        if (message.startsWith("Work")) {

            //@ open WorkerIdleInv(this);
            request = validateAndTokenizeRequest(message);
            if(request == null){
                //@ close WorkerIdleInv(this);
                return;
            }
            //@ open WorkerCommonInv(this);
            log.info("Processing work: " + message);
            //@ close WorkerCommonInv(this);
            
            //@ close ValidRequest(request);
            //@ close WorkerRunningInv(this);
            processWorkRequest();
        } else {
            //@ open WorkerIdleInv(this);
            //@ open WorkerCommonInv(this);
            log.info("Unknown message type received");
            //@ close WorkerCommonInv(this);
            //@ close WorkerIdleInv(this);
        }
    }

    private void processWorkRequest()
    //@ requires WorkerRunningInv(this);
    //@ ensures  WorkerIdleInv(this);
    {
        //@ open WorkerRunningInv(this);
        //@ open WorkerCommonInv(this);
        //@ open ValidRequest(request);
        if(request[1] == null || Integer.parseInt(request[1]) != nodeId){
            //@ close WorkerCommonInv(this);
            request = null;
            //@ close WorkerIdleInv(this);
            return;
        }       

	if(request[2] == null || request[3] == null){
	    //@ close WorkerCommonInv(this);
            request = null;
            //@ close WorkerIdleInv(this);
            return;
	}
	
        int min = Integer.parseInt(request[2]);
        int max = Integer.parseInt(request[3]);
        
        //@ close WorkerCommonInv(this);
        
        if (!validateBounds(min, max)) {
            request = null;
            //@ close WorkerIdleInv(this);
            return;
        }

        int primeCount = countPrimes(min, max);
	
	//@close ValidRequest(request);
	//@close WorkerRunningInv(this);
        std_msgs.String reply = buildWorkReply(primeCount);

        //@ open WorkerRunningInv(this);
        //@ open WorkerCommonInv(this);
        pub.publish(reply);

        //@ close WorkerCommonInv(this);
        request = null;
        //@ close WorkerIdleInv(this);
    }

    private int countPrimes(int min, int max)
    //@ requires min >= 2 &*& min <= max;
    //@ ensures result >= 0;
    {

        int count = 0;

        for (int n = min; n < max; n++)
        //@ invariant min <= n &*& n <= max &*& count >= 0;
        {
            if (isPrime(n) && count < Integer.MAX_VALUE) {
                count++;
            }
        }

        return count;
    }

    private boolean isPrime(int n)
    //@ requires n >= 2;
    //@ ensures true;
    {
        for (int i = 2; i < n/2; i++)
        //@ invariant i >= 2 &*& 2*i <= n + 2;
        {
            if (n % i == 0)
                return false;
        }

        return true;
    }

    private std_msgs.String buildWorkReply(int primeCount)
    //@ requires WorkerRunningInv(this) &*& primeCount >= 0;
    //@ ensures WorkerRunningInv(this) &*& result != null;
    {
    	
    	//@ open WorkerRunningInv(this);
    	//@ open ValidRequest(?request);
        java.lang.String reply = "";
        for (int i = 0; i < request.length; i++)
        //@ invariant i >= 0 &*& i <= request.length &*& array_slice(request, 0, request.length, _); 
        {
            reply += request[i] + " ";
        }
        reply += Integer.toString(primeCount);
        return buildMessage(reply);
        //@ assert array_slice(request, 0, 4, _);
        
        //@ close ValidRequest(request);
        //@ close WorkerRunningInv(this);
    }

    private std_msgs.String buildMessage(java.lang.String message)
    //@ requires WorkerCommonInv(this) &*& message != null;
    //@ ensures WorkerCommonInv(this) &*& result != null;
    {
        //@ open WorkerCommonInv(this);
        std_msgs.String messageWrapper = pub.newMessage();
        //@ close WorkerCommonInv(this);
        messageWrapper.setData(message);

        return messageWrapper;
    }

    private java.lang.String[] validateAndTokenizeRequest(java.lang.String request)
    //@ requires request != null;
    //@ ensures result != null ? result.length == 4 &*& array_slice(result, 0, result.length, _) : result == null;
    {
        java.lang.String[] tokens = request.split(" ");
    	if(tokens.length != 4)
    	    return null;

        //@ assert array_slice(tokens, 0, tokens.length, _);
    	return tokens;
    }

    private boolean validateBounds(int min, int max)
    //@ requires true;
    //@ ensures !result || (min >= 2 && max >= min);
    {
        if (min < 2)
            return false;
        if (max < min)
            return false;

        return true;
    }
}
