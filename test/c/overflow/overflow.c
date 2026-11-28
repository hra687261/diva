/* The overflow of an `int` is undefined behaviour in C: each `+`, `-`, `*` and `/` checks
   that its result fits in 32 bits. With `--entry`, `x + y` and `-x` may overflow, and
   `x / 2` can't: only `INT_MIN / -1` overflows. */
int avg(int x, int y) { return (x + y) / 2; }
int half(int x) { return x / 2; }
int neg(int x) { return -x; }

/* C leaves `a % b` undefined when `a / b` doesn't fit: `INT_MIN % -1`. With `--entry rem`,
   both `y == 0` and that are possible. */
int rem(int x, int y) { return x % y; }
int rem_assign(int x, int y) {
  x %= y;
  return x;
}
int rem10(int x) { return x % 10; }
int main(void) { return 2147483647 + 1; }
