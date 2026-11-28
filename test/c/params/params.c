/* Functions with `int` parameters. Nothing calls them, so they never run. With
   `--entry`, `check` checks them for all the `int`s: `inv 0` divides by zero, `safe`
   can't, because `x * x + 1` is at least 1. */
int avg(int x, int y) { return (x + y) / 2; }
int safe(int x) { return 100 / (x * x + 1); }
int inv(int x) { return 1 / x; }
int main(void) { return 0; }
