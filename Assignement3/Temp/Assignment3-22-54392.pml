/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022

   Problem 2.2, Assignment 3

   Instructor: Antonia Lopes
   Student: Santiago Benites fc54392
   
  This model addresses an implementaion of a basic calling service.
  	-- That the client works through the init function and by sending commands by a channel
  	-- The model is made to whithstand a single connection between the Client and LocalController
    -- The model works by adding commands to be passed to the channel operation1 and operation1 
        for client1 and 2 respectively
	-- The model assumes the existance of a basic calling service
    -- The it allows for 2 way communication
    -- Each client is conneted to a specific localController, and both local controller are 
        connected to the remoteController
    --The communication between Client, LocalController and RemoteController is done by channels
  
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

    chan operation = [0] of {  int };
    chan operation2 = [0] of {  int };

    chan request = [0] of { mtype, int };
    chan request2 = [0] of { mtype, int };

    chan remote = [0] of {  int };
    chan remote2 = [0] of { int };

    run RemoteController(remote);

    //Client1 
    run Client(request,operation);
    run LocalController(request,remote);

    operation ! pickup
    operation ! 9
    operation ! 8
    operation ! 7
    operation ! 6
    operation ! 5
    operation ! click
    operation ! 9
    operation ! 8
    operation ! 7
    operation ! 6
    operation ! 5
    operation ! 4
    operation ! 3
    operation ! 2
    operation ! 1
    operation ! 1
    operation ! ret
    operation ! pickup
    operation ! 9
    operation ! 8
    operation ! 7
    operation ! 6
    operation ! 5
    operation ! 4
    operation ! 3
    operation ! 2
    operation ! 1
    operation ! ret
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
    bool onCall = false;
    
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
    
        insertNumber:
    

            if
            :: onCall == true -> printf("Already in call\n"); goto end;
            :: else -> skip;
            fi

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
            number = 0;
            numberSize = 0;

            if
            :: onCall -> remote!release; remote?callEnded; skip;
            :: !onCall -> goto end;
            fi

            if
            :: callEnded == 0 -> printf("Call not sucefully ended \n"); skip;
            :: callEnded == 1 -> printf("Call sucefully ended \n"); onCall = false; skip;
            fi

            goto end;
    
    
        call:

            
            remote!number;
            byte tone;
            remote ? tone;

    
            if
            :: tone == terminate -> printf("Error Tone...\n");goto end;
            :: tone == complete -> skip;
            fi

            byte toneType;
            remote ? toneType;
            
            if
            :: toneType == 0 -> printf("Busy Tone...\n");goto end;
            :: toneType == 1 -> printf("Valid Tone...\n");skip;
            fi

            remote!start;
            byte answerBool;
            remote?answerBool;

            if
            :: answerBool == false -> printf("Connection Refused...\n");skip;
            :: answerBool == true -> printf("Connection Accepted...\n");printf("Connection Established\n");onCall = true;skip;
            fi

            number = 0;
            numberSize = 0;

    
            goto end


        end:
    
  ::timeout -> printf("Connection has timed out. Disconnecting...\n")
            break
  od ;

}

proctype RemoteController(chan remote){

    int operation2;

    do
    ::

        remote ? operation2 ->
        if
        :: operation2 == start -> goto startR
        :: operation2 == release -> goto releaseR;
        :: else -> goto isValid;
        fi
    

        isValid:
            printf("Checking validity\n");
            byte i = 0;
            bool valid = false;
            for (i in knownNumbers) {
                int num = knownNumbers[i];
                if
                :: num == operation2 -> valid = true;
                :: else -> skip
                fi
            }
            
            if
            :: valid -> remote ! complete; valid = false; goto toneType;
            :: !valid -> remote ! terminate; operation2 = 0;goto end;
            fi 

            goto end

        startR:
            printf("Starting Connection\n")
            
            do
            ::  remote!true; goto end;
            ::  remote!false; goto end;
            od    
            goto end;

        toneType:        

            do
            :: remote!0;goto end;
            :: remote!1;goto end;
            od

            goto end;

        releaseR:

            printf("Ending Call\n")
            byte callEnded = 1;
            do
            ::  remote!1;goto end;
            ::  remote!0;goto end;
            od
            goto end


        end:
    
    od;
}