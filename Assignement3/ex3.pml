# define N 3
# define N_ITER 5
byte n = 0 ;
int finalizedProcesses = 0;
ltl minValue {[] ((finalizedProcesses == N ) -> n >= 2) }


active [ N ] proctype P ( ) {
    byte temp , i = 1 ;
    do
    :: i < N_ITER ->
        reading :   temp = n;
                    temp ++;

        writing :   n = temp;
                    i ++;

        :: else -> break
    od;
    finalizedProcesses ++;
}