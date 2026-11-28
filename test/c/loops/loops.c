/* Loops: a loop is a recursive function of the locals that it assigns. Each iteration
   calls it again with their values, and the loop ends by calling the code after it.
   `check` reports the overflow of the sums: the intervals of a loop are widened, and
   nothing bounds a sum (`i` is bounded by `i < 5`). Relations between the locals, such
   as `s <= i * i * i`, would be needed. */
int sum(int n) {
  int s = 0;
  for (int i = 1; i <= n; i++) s += i;
  return s;
}

int digits(int n) {
  int d = 1;
  while (n >= 10) {
    n = n / 10;
    d++;
  }
  return d;
}

int main(void) {
  int s = 0;
  int i = 0;
  do {
    s += i * i;
    i++;
  } while (i < 5);
  int t = 0;
  for (int k = 0; k < 10; k++) t += k;
  int n = 12345;
  int d = 1;
  while (n >= 10) {
    n = n / 10;
    d++;
  }
  return s * 10000 + t * 10 + d;
}
