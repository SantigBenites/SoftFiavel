/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */

byte    n = 0;

active proctype P() {
	byte R1 = n;
	R1 = R1 + 1;
    	n = R1;
	printf("Process P, n = %d\n", n)
}

active proctype Q() {
	byte R1 = n;
	R1 = R1 + 1;
    	n = R1;
	printf("Process Q, n = %d\n", n)
}

