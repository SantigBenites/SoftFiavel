byte x = 0;
  
active proctype P() {
  do
  :: x < 6 -> x++;  printf("x = %d\n", x)
  :: x > 0 ->  x--; printf("x = %d\n", x)
  :: else -> x = 3; printf("x = %d\n", x)
  od
}

active proctype Monitor(){
	atomic{ !(0 <= x && x <= 6) -> assert(false) }
}