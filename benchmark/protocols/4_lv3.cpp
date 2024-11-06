/*
* Patch: https://github.com/CTL-Datalog/Dataset/blob/main/lv3/patch.diff#L71
*/

#define NULL __null

struct in_addr{
    unsigned int s_addr;
};

class Port {
public:
  Port(unsigned short int num){

  }
};

class Destinations {

public:
  unsigned char isTCP;
  struct in_addr addr;
  Port rtcpPort;
  int tcpSocketNum;
  unsigned char rtpChannelId, rtcpChannelId;
};

class RTPSink {


public:
    void removeStreamSocket(int sockNum, unsigned char streamChannelId) {

    }

    int envir() {};
};

class RTCPInstance{

public:
  void removeStreamSocket(int sockNum, unsigned char streamChannelId) {}

  void unsetSpecificRRHandler(unsigned int fromAddress, Port fromPort) {}
};

class Groupsock{

public:
void removeDestination(unsigned sessionId) {}
};

int clearServerRequestAlternativeByteHandler( int a, int b){}

/*@ AG( (!(fRTPSink=0))  => AF(clearServerRequestAlternativeByteHandler())) 
@*/

RTCPInstance* _nondet_int(void);
Destinations* __VERIFIER_nondet_int(void);

int main(){
    Destinations* dests =  __VERIFIER_nondet_int();
    unsigned clientSessionId;
    RTPSink* fRTPSink;
    RTCPInstance* fRTCPInstance= _nondet_int(); 
    Groupsock* fRTPgs;
    Groupsock* fRTCPgs;

  if (dests) {
    if (fRTPSink != NULL) {
      // To Martin: the correct version is to uncomment the following line!
      //clearServerRequestAlternativeByteHandler(fRTPSink->envir(), dests->tcpSocketNum);
      fRTPSink = NULL;
      fRTPSink->removeStreamSocket(dests->tcpSocketNum, dests->rtpChannelId);
    }
    if (fRTCPInstance != NULL) {
      fRTCPInstance->removeStreamSocket(dests->tcpSocketNum, dests->rtcpChannelId);
      fRTCPInstance->unsetSpecificRRHandler(dests->tcpSocketNum, dests->rtcpChannelId);
    }
  } 
}
//add clearServerRequestAlternativeByteHandler(7).
