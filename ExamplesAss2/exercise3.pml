active proctype P() {
  byte x = 0;
  do
  :: x < 6 -> x++;  printf("x = %d\n", x)
  :: x > 0 ->  x--; printf("x = %d\n", x)
  :: else -> assert(false); x = 3; printf("x = %d\n", x)
  od
}
