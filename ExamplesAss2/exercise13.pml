/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2021

   Instructor: Antonia Lopes
  
  	Alternating Bit Protocol

  	Credits:  G. J. Holzmann
  	"The Verification of Concurrent Systems", pages 102 - 103.

*/

#define NLOSS 0  /* Set NLOSS to 1 if no messages should be lost.              */
			     /* Set NLOSS to 0 if the model should simulate lost messages. */

#define MAX 6               

#if NLOSS

/*********************************************************************

A model of the Alternating Bit Protocol considering that channels are
not lossy.

**********************************************************************/

// for sending message and bit from A to B
chan AtoB = [2] of { byte, bit };

// for sending ack from B to A
chan BtoA = [2] of { bit };

active proctype SenderA () {
	bit seq_out = 1, seq_in;
	byte msg = 0;
  
	do
	::  AtoB!msg, seq_out ->
snd:    	BtoA?seq_in;
           	if
            :: seq_in == seq_out ->
progress:       	d_step{ seq_out = 1 - seq_out; msg = (msg+1)%MAX }
            :: else -> 
            		skip
           	fi
	od
}

active proctype ReceiverB () {
	bit seq_in, old; 
	byte msg; 
	
	//receive first message
	AtoB?msg, seq_in -> 
		BtoA!seq_in;
		goto transmit;
		
	//subsequent messages
	do
    :: AtoB?msg, seq_in ->
rcv:   		BtoA!seq_in;			//send ack
			if 
			:: seq_in != old -> 
transmit:			old = seq_in;	//transmit msg	
			:: else ->  			
					skip			//discard msg	
			fi	
  od
}


#else


/*********************************************************************

A model of the Alternating Bit Protocol + lossy channels.

The model has  some ghost variables and assertions, introduced
for verification purposes.

**********************************************************************/

// for sending message and bit from A to B
chan AtoB = [2] of { byte, bit };

// for sending ack from B to A
chan BtoA = [2] of { bit };

active proctype SenderA () {
	bit seq_out = 1, seq_in;
	byte msg = 0;
  
	do
	::  AtoB!msg, seq_out ->
snd:    do 
		:: BtoA?seq_in ->
           		if
             	:: seq_in == seq_out ->
progress:       		d_step{ seq_out = 1 - seq_out; msg = (msg+1)%MAX }
             	:: else -> 
             		skip
           		fi;
           		break
        :: BtoA?_ -> 
progressL: lossA:        	skip;  // message ack loss
       od
	od
}

active proctype ReceiverB () {
	bit seq_in, old; 
	byte msg, expected_msg = 0; 
	
	//receive first message
	do 
	:: AtoB?msg, seq_in -> 
			BtoA!seq_in;
			goto transmit;
	:: AtoB?_, _ ->
       		skip	// message msg loss
	od
		
	//subsequent messages
	do
    :: AtoB?msg, seq_in ->
rcv:   		BtoA!seq_in;			//send ack
			if 
			:: seq_in != old -> 
transmit:			atomic{  		//transmit msg
						old = seq_in;	
						assert(msg == expected_msg);
						expected_msg = (expected_msg+1)%MAX
					}
			:: else ->  			
					skip; 			//discard msg	
			fi	
    :: AtoB?_, _ ->
progressL: lossM:      skip			// message msg loss 
    :: timeout ->
       		BtoA!seq_in
  od
}

#endif

/*********************************************************************

Important properties are:

1) Every message is transmitted only once
2) Order of messages is preserved (transmitted in the same order than sent by A)
3) Every message is eventually sent and received sooner or later

Assertions in the model allow us to verify the preservation of order 
and uniqueness (1 and 2)

For 3) we could consider 
   []((SenderA@snd && SenderA:msg == N) -> <>(ReceiverB@rcv && ReceiverB:msg == N)) }
for some N in 0..MAX-1 (for symmetry reasons, we can choose an arbitrary N)
This property is violated because of computations with infinitely many message/ack loss 
events.

We could instead check if there are no progress cycles and see again we get one of these 
executions with infinitely many message/ack loss events. 
We could also see how many  non-progress cycles are there with  
	$ gcc -DMEMLIM=1024 -O2 -DXUSAFE -DNP -DNOCLAIM -DNOREDUCE -w -o pan pan.c
	$ ./pan -l -c0
	State-vector 64 byte, depth reached 125, errors: 54
inspect them and conclude that they all have the same characteristics.
Since they are too many, we can instead use this tip from Promela Reference Manual:

"Progress labels ... can, however, also be used during verifications 
to eliminate harmless variations of liveness violations. One such application, 
can be to mark message loss events with a pseudo progress label, to indicate that 
sequences that contain infinitely many message loss events are of secondary 
interest. If we now search for non-progress executions, we will no longer 
see any executions that involve infinitely many message loss events."

 
If we also add progress labels in front of the loss labels, we will get rid of all
progress cycles that we got caused by infinitely many message/ack loss 
events. The progress cycles are now executions that do not involve infinitely 
many message loss events nor infinitely many message transmittions.  

	$gcc -DMEMLIM=1024 -O2 -DXUSAFE -DNP -DNOCLAIM -DNOREDUCE -w -o pan pan.c
	$./pan -m10000  -l

	Full statespace search for:
		never claim         	+ (:np_:)
		assertion violations	+ (if within scope of claim)
		non-progress cycles 	+ (fairness disabled)
		invalid end states	- (disabled by never claim)

	State-vector 64 byte, depth reached 125, errors: 0

The absence of progress cycles proves that provided that we do not have infinitely 
many message loss events, we will have infinitely many message transmissions.

**********************************************************************/