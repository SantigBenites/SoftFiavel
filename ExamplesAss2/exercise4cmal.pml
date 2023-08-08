/* Copyright 2007 by Moti Ben-Ari under the GNU GPL; see readme.txt */
/* Adapted by Antonia Lopes */

byte n = 0;

proctype P() {
  byte R1;
  R1 = n + 1;
  n = R1;
  printf("Process P, n = %d\n", n)
}

proctype Q() {
  byte R1;
  R1 = n + 1;
  n = R1;
  printf("Process Q, n = %d\n", n);
}

init{
	atomic { run P(); run Q()};
	_nr_pr == 1 -> assert (n == 1 || n == 2);
}

