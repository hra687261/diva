/* `return`, `break` and `continue` in the middle of the code. `return` ends the function,
   `break` calls the code after the loop, and `continue` starts the next iteration (after
   the step of a `for`, or at the test of a `do`). */
int smallest_divisor(int n) {
  for (int d = 2; d < n; d++)
    if (n % d == 0) return d;
  return n;
}

int main(void) {
  int odd = 0;
  for (int i = 0; i < 10; i++) {
    if (i % 2 == 0) continue;
    odd += i;
  }
  int k = 0;
  while (1) {
    k++;
    if (k * k > 50) break;
  }
  int j = 0;
  do {
    j++;
    if (j < 3) continue;
    break;
  } while (1);
  return odd * 10000 + k * 100 + j;
}
