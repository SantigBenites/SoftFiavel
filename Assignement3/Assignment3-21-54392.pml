/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022

   Problem 2.1, Assignment 3

   Instructor: Antonia Lopes
   Student: Santiago Benites fc54392
   
  This model addresses an implementation of a single phone.
  	-- That the client works through the init function and by sending commands by a channel
  	-- The model is made to whithstand a single connection between the Client and LocalController
    -- The model works by adding commands to be passed to the channel operation
	-- 
  
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
#define answer        24
#define release       25

//properties 

ltl validPhoneNum {[] (globalPhoneSize < 5) };


//////////////////////////////	
// Algorithm
//////////////////////////////	

// ghost vars
int globalPhoneSize = 0;


// global vars
//chan request = [0] of { mtype, int };
//int Client1[15] = {pickup,9,8,7,6,click,5,4,3,2,1};

// init, if required
init {

  chan operation = [0] of {  int };
  chan request = [0] of { mtype, int };

  //Client
  run Client(request,operation);
  run LocalController(request);

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

}

proctype Client(chan request;chan operations){

  byte i;
  int operation;
  bool onHook = true;
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

  ::timeout -> printf("Client has timed out. Disconnecting...\n")
            break

  od;

}

proctype LocalController(chan request){

  byte operation;
  int number;
  int numberSize = 0;

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

      number = 0;
      numberSize = 0;
      printf("Phone number reset \n")
      goto end;


    call:

      do
      :: printf("Busy tone...\n") -> break  
      :: printf("Ring tone...\n") -> break
      od


      number = 0;
      numberSize = 0;
 
      goto end;

    end:

      globalPhoneSize = numberSize;

  ::timeout -> printf("Local has timed out. Disconnecting...\n")
            break
  od ;

}