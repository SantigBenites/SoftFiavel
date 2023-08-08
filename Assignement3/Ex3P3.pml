/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022

   Problem 2.2, Assignment 3

   Instructor: Antonia Lopes
   Student: Santiago Benites
   
  This model addresses an implementaion of a basic calling service.
  	-- That the client works through the init function and by sending commands by a channel
  	-- The model is made to whithstand a single connection between the Client and LocalController
    -- The model works by adding commands to be passed to the channel operation1 and operation1 
        for client1 and 2 respectively
	-- The model assumes the existance of a basic calling service
    -- The it allows for 2 way communication
    -- Each client is conneted to a specific localController, and both local controller are 
        connected to the remoteController
    -- The communication between Client, LocalController and RemoteController is done by channels
    -- For a number to be considered valid it needs to be present in knownNumbers
  
*/

//////////////////////////////	
// model parameters
//////////////////////////////

// macros below define XX to have the value Y,
// unless a different value is defined on the command line 
// when Spin is invoked  
// $ spin -DXX=4 -a model.pml

// number of processes
#ifndef  N
#define  N  3
#endif

// numbers available 
#ifndef  LIMIT
#define  LIMIT  5
#endif


//////////////////////////////	
// LTL properties 
//////////////////////////////	

//symbol definitions

#define pickup  11
#define click   12
#define ret     13

#define start         21
#define complete      22
#define confirmation  23
#define denial        24
#define accept        25
#define release       26
#define terminate     27

#define MAXSIZE 11

//properties 

// ltl name { formula }; // uncomment for task 1 


//////////////////////////////	
// Algorithm
//////////////////////////////	

// ghost vars


// global vars
//chan request = [0] of { mtype, int };
//chan remote = [0] of {  int };
//chan remote2 = [0] of { int };
//int Client1[MAXSIZE] = {pickup,9,8,7,6,5,4,3,2,1};
int knownNumbers[MAXSIZE] = {987654321,123456789}


// init, if required
init {

    chan operation1 = [0] of {  int };
    chan operation2 = [0] of {  int };

    chan request = [0] of { mtype, int };
    chan request2 = [0] of { mtype, int };

    chan remote = [0] of {  int };
    chan remote2 = [0] of { int };

    run RemoteController(remote,remote2);

    //Client1 
    run Client(request,operation1);
    run LocalController(request,remote);

    //Client2
    run Client(request2,operation2);
    run LocalController(request2,remote2);

    operation2 ! pickup
    operation2 ! 9
    operation2 ! 8
    operation2 ! 7
    operation2 ! 6
    operation2 ! 5
    operation2 ! 4
    operation2 ! 3
    operation2 ! 2
    operation2 ! 1
    operation2 ! ret

    operation1 ! pickup
    operation1 ! ret

}

proctype Client(chan request;chan operations){

  byte i;
  bool onHook = true;
  int operation;

  do
  ::
    operations?operation;

    if
    :: operation == pickup  -> goto pickupC    // pickup
    :: operation == click   -> goto clickC      // click
    :: operation == ret     -> goto retC          // return
    :: (operation == 1 || operation == 2 || operation == 3 || 
       operation == 4 || operation == 5 || operation == 6 || 
       operation == 7 || operation == 8 || operation == 9) -> goto insertNumberC;
    :: else -> goto endC;
    fi
    
    insertNumberC:

      if
      :: onHook -> printf("phone not picked up\n");goto endC;
      :: !onHook -> goto sendOp;
      fi;

    pickupC:

      if
      :: onHook -> printf("Phone picked up \n");printf("Dial tone... \n"); onHook = false; goto sendOp;
      :: !onHook -> printf("Phone already picked up \n"); goto endC;
      fi;

    clickC:

      if
      :: onHook -> printf("Phone is on hook\n"); goto endC;
      :: !onHook -> goto sendOp;
      fi;

    retC:

      if
      :: !onHook -> printf("Phone put on hook \n");onHook = true; goto sendOp;
      :: onHook -> printf("Phone already on hook \n"); goto endC;
      fi;


    sendOp:
      request ! operation;
      goto endC;

    endC:
  
  od;
  
}

proctype LocalController(chan request;chan remote){

    int operation;
    int number;
    int numberSize = 0;
    bool acceptingMessages = 1;
    bool onCall = false;
    bool endCall = true;
    
    do
    ::
    
        request?operation ->
        if
        :: operation == pickup -> goto pickupS  // pickup
        :: operation == click -> goto clickS   // click
        :: operation == ret -> goto retS  // return
        :: (operation == 1 || operation == 2 || operation == 3 || 
           operation == 4 || operation == 5 || operation == 6 || 
           operation == 7 || operation == 8 || operation == 9) -> goto insertNumber;
        :: else -> skip;
        fi

    ::
        remote?operation ->
        if
        :: operation == complete -> goto completeS  // return
        :: operation == terminate -> goto terminateS
        :: else -> goto end;
        fi
    
        insertNumber:
    
            number =  number * 10 + operation;
            numberSize++;
            printf("Current cellphone number is %d\n", number);

            if
            :: numberSize == 9 -> goto call;
            :: else -> skip;
            fi

            goto end;
    
        pickupS:
    
            goto end;
        
        clickS:
    
            number = 0;
            numberSize = 0;
            printf("Click..., phone number reset \n")
            goto end;
    
        retS:
    
            printf("Phone number reset \n");
            byte callEnded;
            if
            :: onCall -> remote!release; remote?callEnded; skip;
            :: !onCall -> goto end;
            fi

            if
            :: callEnded == 0 -> printf("Call not sucefully ended \n"); skip;
            :: callEnded == 1 -> printf("Call sucefully ended \n"); skip;
            fi

            onCall = false;
            number = 0;
            numberSize = 0;

            goto end;
    
    
        call:

            number = 0;
            numberSize = 0;

            remote!number;
            byte tone;
            remote ? tone;
    
            if
            :: tone == 0 -> printf("Error Tone...\n");goto end;
            :: tone == 1 -> printf("Valid Tone...\n");skip;
            fi

            remote!start;
            byte answerBool;
            remote?answerBool;

            if
            :: answerBool == false -> printf("Connection Refused...\n");goto end;
            :: answerBool == true -> printf("Connection Accepted...\n");skip;
            fi

            printf("Connection Established\n");
            onCall = true;

    
            goto end

        completeS:

            printf("Choosing message\n");
            if
            :: acceptingMessages == 1 -> remote!confirmation; remote!accept; skip;
            :: acceptingMessages == 0 -> remote!confirmation; remote!denial; skip;
            :: else -> skip
            fi

            onCall = true;

            goto end
    
        terminateS:
            remote!endCall;
            printf("Connection Ending\n");
            onCall = false;
            goto end

        end:
    
  ::timeout -> printf("Connection has timed out. Disconnecting...\n")
            break
  od ;

}

proctype RemoteController(chan remote1;chan remote2){

    int operation2;
    bool valid = false;
    bool boolVal = 0;
    int connectionStatus = 0;

    do
    ::

        remote1 ? operation2 ->
        if
        :: operation2 == start -> goto startR1
        :: operation2 == confirmation -> goto confirmationR2
        :: operation2 == release -> goto releaseR1;
        :: else -> goto isValid1;
        fi
    ::

        remote2 ? operation2 ->
        if
        :: operation2 == start -> goto startR2
        :: operation2 == confirmation -> goto confirmationR1
        :: operation2 == release -> goto releaseR2;
        :: else -> goto isValid2;
        fi

        isValid1:
            printf("Checking validity\n");
            byte i = 0;
            for (i in knownNumbers) {
                if
                :: knownNumbers[i] == operation2 -> valid = true;
                :: else -> skip
                fi
            }

            if
            :: valid -> remote1 ! 0; skip
            :: !valid -> remote1 ! 1; operation2 = 0;
            fi 

            goto end

        startR1:
            printf("Starting Connection\n")
            remote2!complete
            goto end;

        confirmationR1:
            printf("Confirmation by Remote2\n")
            
            remote2 ? connectionStatus;
            if
            :: connectionStatus == accept -> remote1!1; goto end;
            :: connectionStatus == denial -> remote1!0; goto end;
            fi


        releaseR1:

            printf("Ending Call\n")
            byte callEnded;
            remote2 ! terminate;
            remote2 ? callEnded;
            if
            :: callEnded == 1 -> remote1!1;skip
            :: callEnded == 0 -> remote1!0;skip
            fi
            goto end

        
        isValid2:
            printf("Checking validity\n");
            byte j = 0;
            for (j in knownNumbers) {
                if
                :: knownNumbers[j] == operation2 -> valid = true;
                :: else -> skip
                fi
            }

            if
            :: valid -> remote2 ! 0; skip
            :: !valid -> remote2 ! 1; operation2 = 0;
            fi 

            goto end

        startR2:
            printf("Starting Connection\n")
            remote1!complete
            goto end;

        confirmationR2:
            printf("Confirmation by Remote1\n")
            
            remote1 ? connectionStatus;
            if
            :: connectionStatus == accept -> remote2!1; goto end;
            :: connectionStatus == denial -> remote2!0; goto end;
            fi


        releaseR2:

            printf("Ending Call\n")
            byte callEnded2;
            remote1 ! terminate;
            remote1 ? callEnded2;
            if
            :: callEnded2 == 1 -> remote2!1;skip
            :: callEnded2 == 0 -> remote2!0;skip
            fi
            goto end

        end:
    
    od;
}