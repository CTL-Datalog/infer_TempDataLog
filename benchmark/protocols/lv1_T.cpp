/*
Patch: https://github.com/CTL-Datalog/Dataset/blob/main/lv1/patch.diff#L106-L109
*/

# include <iostream>

class RTSPClientConnection {
  
};

void handleHTTPCmd_notSupported() {
  
}

/*@ AG((prevClientConnection = 0) \/ (prevClientConnection = this_)  => AF(Return(0))) 
@*/

RTSPClientConnection* _nondet_int(void);


int main(){
  RTSPClientConnection *prevClientConnection;
  bool fIsActive;
  RTSPClientConnection *this_ ; //=  _nondet_int(); 

  
  if (prevClientConnection == NULL||prevClientConnection == this_) {
    // There was no previous HTTP "GET" request; treat this "POST" request as bad:
    handleHTTPCmd_notSupported();
    fIsActive = false; // triggers deletion of ourself
    return false;
  }

}