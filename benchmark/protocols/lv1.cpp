/*
Patch: https://github.com/CTL-Datalog/Dataset/blob/main/lv1/patch.diff#L106-L109
*/

# include <iostream>

class RTSPClientConnection {
  
};

void handleHTTPCmd_notSupported() {
  
}

/*@ AG((prevClientConnection = 0) \/ (prevClientConnection = this) => AF(handleHTTPCmd_notSupported())) @*/


int main(){
  RTSPClientConnection *prevClientConnection;
  bool fIsActive;
  
  if (prevClientConnection == NULL) {
    // There was no previous HTTP "GET" request; treat this "POST" request as bad:
    handleHTTPCmd_notSupported();
    fIsActive = false; // triggers deletion of ourself
    return false;
  }
}