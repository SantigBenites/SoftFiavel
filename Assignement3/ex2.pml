#define N 2
#define N_ITER 5
byte n = -2 ;

//ltl smallerThan20{[] (n < 20)};
//ltl twoNotTwoAgainTwo{n == 2 U ([] (n!=2)) };
//ltl largerThanZerotheAlways {<> ([] (n > 0))}

active [N] proctype P ( ) {
    byte temp , i = 1 ;
    do
    :: i < N_ITER ->
        reading :   //assert(temp <= n);
                    temp = n;
                    temp ++;
            
        writing :   //assert(temp >= n)
                    n = temp;
                    i ++;
        
    :: else -> break
    od
}
