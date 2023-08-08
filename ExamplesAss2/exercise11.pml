/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2021

   Instructor: Antonia Lopes
   
   This model addresses mutual exclusion with clients communicating through
   shared memory with a resource manager, following a specific protocol.
   
   The model is for 3 clients and a manager whose behaviour, in the presence 
   of requests for different clients to use the resource, is non-deterministic
   
   The model assumes that a read that overlaps a write always get either the old or 
   the new value
   
*/


//////////////////////////////	
// Model
//////////////////////////////

bool r[3]; //for requesting the use of resource, written by client and read by manager
bool g[3]; //for granting the resource, read by client and written by manager

proctype ResourceManager(){
		do 
		:: r[0] && !g[0] && !g[1] && !g[2] -> g[0]=true;
		:: r[1] && !g[0] && !g[1] && !g[2] -> g[1]=true;
		:: r[2] && !g[0] && !g[1] && !g[2] -> g[2]=true;
		:: g[0] && !r[0] -> g[0]=false;
		:: g[1] && !r[1] -> g[1]=false;
		:: g[2] && !r[2] -> g[2]=false;
		od
}

proctype Client(int i){
again:	
		do 			/* does other stuff, possibly never needs to use the resource */
		:: true ->skip
		:: true -> break
		od;
		!g[i] -> r[i] = true;  /* asks the resource  but only after
							   the manager ack previous release  */
		g[i] -> printf("Client %d using the resource",i); /* uses the resource */
		r[i] = false;  /* frees the resource */
		goto again;
}

init{
	atomic { 
		run ResourceManager(); 
		run Client(0); run Client(1); run Client(2) 
	}
}

//////////////////////////////	
// LTL properties 
//////////////////////////////	

#define I 0
#define J 1

#define REQUESTED (r[0] || r[1] || r[2])
#define GRANTED (g[0] || g[1] || g[2])
#define STABLE_STATE (!REQUESTED && !GRANTED)

#define NR_NG (!r[I] && !g[I])
#define R_NG  (r[I] && !g[I])
#define R_G   (r[I] && g[I])
#define NR_G  (!r[I] && g[I])

/*---------------------------------------------------------------------------------------
	mutual exclusion - valid
---------------------------------------------------------------------------------------*/
ltl me { [](g[0] -> !g[1] && !g[2]) && 
		 [](g[1] -> !g[0] && !g[2]) && 
		 [](g[2] -> !g[1] && !g[0]) }

/*---------------------------------------------------------------------------------------
	mutual exclusion again, exploring separability
---------------------------------------------------------------------------------------*/
ltl me0 { [](g[0] -> !g[1] && !g[2]) }
ltl me1 { [](g[1] -> !g[0] && !g[2]) }
ltl me2 { [](g[2] -> !g[0] && !g[1]) }

 
/*---------------------------------------------------------------------------------------
	behaviour of the system adheres to the protocol - valid
	
	Confirm that it is essential that the client waits for the ack of the release before 
	asking the resource again.
	
	Notice that, although [](a -> aWb) is a safety property, Spin converts it into
		[](!a || []a || a U b)
	and, hence, violations of this property are reported though counter-examples
	that include a cycle.
---------------------------------------------------------------------------------------*/

ltl prtc1 { [](NR_NG -> (NR_NG W R_NG)) }
ltl prtc2 { [](R_NG -> (R_NG W R_G)) }
ltl prtc3 { [](R_G -> (R_G W NR_G)) }
ltl prtc4 { [](NR_G -> (NR_G W NR_NG)) }


/*---------------------------------------------------------------------------------------
	bounded overtaking - as expected, invalid
	for this to be valid, we need a manager that decides which client gets the resource   

	Spin sources need to be compiled with the preprocessor directive -DNXT 
	so the set of temporal operators is extended with the unary operator: X (next). 
---------------------------------------------------------------------------------------*/

ltl bot { []( (!r[I] && X r[I]) -> (!g[J] W (g[J] W (!g[J] W g[I]))) ) }

/*---------------------------------------------------------------------------------------
	stability says that whenever the system is in a state different from STABLE_STATE 
	sooner or later it leaves that state
	
	stability is difficult to specify as it requires to write too many formulas
	instead, we specify a property stronger than stability (that implies it) 
	if this property is valid, then stability also holds 
	
	we explore that whenever the system is in a state different from STABLE_STATE
	either  GRANTED or REQUESTED && !GRANTED
	    
	stronger than stability - valid under weak fairness
---------------------------------------------------------------------------------------*/
ltl sstability1 { []( (REQUESTED && !GRANTED) -> <> GRANTED )}
ltl sstability2 { []( GRANTED -> <>!GRANTED )}
