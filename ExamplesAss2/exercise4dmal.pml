/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Adapted by A Lopes */

byte n = 0;
bool printedTwo = 0;

active proctype P() {
  byte R1;
  R1 = n + 1;
  n = R1;
  atomic{ 
  	printf("Process P, n = %d\n", n);
  	if 
  	:: n == 2 -> printedTwo = 1
  	:: n == 1 && printedTwo -> assert false
  	:: else -> skip
  	fi
  }
}

active proctype Q() {
  byte R1;
  R1 = n + 1;
  n = R1;
  atomic{ 
  	printf("Process Q, n = %d\n", n);
  	if 
  	:: n == 2 -> printedTwo = 1
  	:: n == 1 && printedTwo -> assert false;
  	:: else -> skip
  	fi
  }
}
