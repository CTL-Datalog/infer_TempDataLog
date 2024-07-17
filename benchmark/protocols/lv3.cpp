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

/*@ AG( (_dests_isTCP >0) /\ (!(fRTPSink=0))   => AF(clearServerRequestAlternativeByteHandler())) 
@*/

int main(){
    Destinations* dests;
    unsigned clientSessionId;
    RTPSink* fRTPSink;
    RTCPInstance* fRTCPInstance;
    Groupsock* fRTPgs;
    Groupsock* fRTCPgs;

  if (dests->isTCP>0) {
    if (fRTPSink != NULL) {
      //clearServerRequestAlternativeByteHandler(fRTPSink->envir(), dests->tcpSocketNum);
      fRTPSink->removeStreamSocket(dests->tcpSocketNum, dests->rtpChannelId);
    }
    if (fRTCPInstance != NULL) {
      fRTCPInstance->removeStreamSocket(dests->tcpSocketNum, dests->rtcpChannelId);
      fRTCPInstance->unsetSpecificRRHandler(dests->tcpSocketNum, dests->rtcpChannelId);
    }
  } else {
    // Tell the RTP and RTCP 'groupsocks' to stop using these destinations:
    if (fRTPgs != NULL) fRTPgs->removeDestination(clientSessionId);
    if (fRTCPgs != NULL && fRTCPgs != fRTPgs) fRTCPgs->removeDestination(clientSessionId);
    if (fRTCPInstance != NULL) {
      fRTCPInstance->unsetSpecificRRHandler(dests->addr.s_addr, dests->rtcpPort);
    }
  } 
}
