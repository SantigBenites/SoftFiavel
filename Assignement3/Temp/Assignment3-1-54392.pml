/*
   Software Reliability Course
   Masters Course on CSE
   Ciencias.ULisboa
   Fall 2022

   Problem 1, Assignment 3

   Instructor: Antonia Lopes
   Student: Santiago Benites fc54392
   
    This model implements a simple read write cycle, but unlike the previous 
    exercises it makes use of concurrency management
  
*/

#define N 2
#define N_ITER 5
#define N_MAX (N * (N_ITER - 1))
byte n = 0 ;
int finalizedProcesses = 0;

bool wantC = false;

ltl maxValue {[] ((finalizedProcesses == N) -> n == N_MAX)}
//ltl smallerThan20{[] (n < 20)};
//ltl twoNotTwoAgainTwo{n == 2 U ([] (n!=2)) };
//ltl largerThanZerotheAlways {<> ([] (n > 0))}

active [N] proctype P ( ) {
    byte temp , i = 1 ;
    do
    :: i < N_ITER -> 
        
        atomic{
            !wantC
            wantC = true
        }
        

        reading: //assert(temp <= n);
                 temp = n ;
                 temp ++;

        writing: //assert(temp >= n);
                 n = temp ;
                 i ++
                 
        wantC = false;
        
    :: else -> break
    od
    finalizedProcesses++;
}
