/* Locals: each assignment gives the local a new value, which the code after it sees. A
   block has its own locals: the inner `x` hides the outer one, and after the block the
   outer one is seen again. A local without a value is 0 for DIVA (C leaves it undefined). */
int main(void) {
  int x = 3;
  int y;
  y = x * 2;
  x += y;
  x++;
  {
    int x = 100;
    y = y + x;
    x--;
  }
  return x * 1000 + y;
}
