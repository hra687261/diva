/* Conditions: comparisons, `&&`, `||` and `!`, and `c ? a : b`. A comparison is `1` or
   `0`. `&&` computes its right side only if it needs it: in `main`, `1 / 0` never runs,
   and with `--entry big`, `y > 0 && x / y > 1` can't divide by zero. Its division is
   still reported as a possible overflow: intervals divide only by constants for now.
   `y != 0` wouldn't do: an interval can't say that `y` isn't 0. */
int big(int x, int y) { return y > 0 && x / y > 1; }
int max(int a, int b) { return a > b ? a : b; }
int sign(int x) { return x < 0 ? -1 : (x > 0); }
int main(void) { return (7 > 3) * 100 + (4 > 9 ? 4 : 9) * 10 + !0 + (0 && 1 / 0); }
