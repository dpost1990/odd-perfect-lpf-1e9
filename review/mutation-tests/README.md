# Mutation tests (B = 10^6)

Deliberately corrupted inputs, used to check that `review/tree_check.py` catches errors.
The baseline is the B = 10^6 run, which you can rebuild with `make check-small`.

| file | corruption | tree_check.py result |
|---|---|---|
| `delA_0.log`, `delA_1.log`, `delA_2.log` | a block of assignment events deleted from the proof log | FAIL (errors=1) |
| `lb2ub.log` | a lower-bound leaf (`LB`) relabelled as an upper-bound leaf (`UB`) | FAIL (errors=1) |
| `xprime.log` | an exclusion node on the wrong prime (`X 11` changed to `X 13`) | FAIL (errors=15) |
| `rows_drop.txt` | an admissible exponent (a = 4) removed from a row | rejected (missing exponent, KeyError) |
| `rows_fac.txt` | a wrong exponent in one row factorisation (2^1 changed to 2^2) | rejected (`factorization wrong`) |
| `mup_small.txt`, `mup_tiny_lower.txt` | a smaller value for the bound M (by a factor of 2^10, and slightly) | **not** detected by tree_check.py |

`tree_check.py` does not check the bound M. It reads M from the file written by `mup_check.c`.
That bound is computed independently by `mup_check.c`, and again inside `replay.py` with a different method.

At B = 10^9 the two values agree:

- 18.454845971372 from `mup_check.c`
- 18.454845971306 from `replay.py`

Both are rigorous upper bounds.
