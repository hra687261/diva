/* `if`: the code after it is a function of the locals that the branches assign, called at
   the end of each branch. So after the `if`, the analysis knows the values of each branch:
   in `main`, `b` is 10, and `1 / b` never runs. */
int clamp(int x, int lo, int hi) {
  int r = x;
  if (x < lo) r = lo;
  else if (x > hi) r = hi;
  return r;
}

int main(void) {
  int a = 5;
  int b = 0;
  if (a > 3) {
    b = a * 2;
    a = 1;
  } else
    b = 7;
  if (b == 0) return 1 / b;
  return a * 100 + b;
}
