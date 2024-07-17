/*
Patch: https://github.com/CTL-Datalog/Dataset/blob/main/lv1/patch.diff#L106-L109
*/

# include <iostream>

class RTSPClientConnection {
  
};

void handleHTTPCmd_notSupported() {
  
}

/*@ AG((prevClientConnection = 0) \/ (prevClientConnection = this_)  => AF(handleHTTPCmd_notSupported())) 
@*/

RTSPClientConnection* _nondet_int(void);


int main(){
  RTSPClientConnection *prevClientConnection;
  bool fIsActive;
  RTSPClientConnection *this_ ; //=  _nondet_int(); 

  
  if (prevClientConnection == NULL) { 
    // There was no previous HTTP "GET" request; treat this "POST" request as bad:
    handleHTTPCmd_notSupported();
    fIsActive = false; // triggers deletion of ourself
    return false;
  }
  else if (prevClientConnection == this_) {
    // To Martin: the correct version is to uncomment the following line!
    //handleHTTPCmd_notSupported();
  }
  else {}
}