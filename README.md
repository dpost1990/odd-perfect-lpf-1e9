# Largest prime factor of an odd perfect number > 10^9 (candidate result)

**Claim (computer-assisted, awaiting expert review).** No odd integer N > 1 with all prime factors ≤ 10^9 satisfies σ(N) = 2N. So every odd perfect number,
if one exists, has a prime factor greater than 10^9.

**Status: candidate result, not yet peer reviewed.**
- The previous record is 10^8 (Goto & Ohno, *Math. Comp.* 77 (2008), 1859–1868).
- This repository holds:
  - the search program;
  - the full proof certificate for B = 10^9;
  - three independently written checkers, with their outputs.
- Expert feedback is very welcome; please open an issue.

**Disclosure.** I am not a professional number theorist. The code and the checkers were developed with substantial help
from AI agents (Anthropic's Claude). The safeguard is that each checker was written independently of the search
code and verifies the certificate in its own way, as described below.

— Dave Post, November 2026

---

## Results

| B | nodes | rows (primes with cyclotomic data) | search time | checks |
|---|---|---|---|---|
| 10^4 | 124 | 71 | 0.0 s | replay, all rows recomputed |
| 10^6 | 562 | 290 | 3.3 s | replay, tree check, all rows recomputed, identical to the Python prototype |
| 10^7 | 1 276 | 665 | 56 s | replay, tree check, identical exact-arithmetic variant |
| 10^8 | 3 097 | 1 625 | 1 402 s (≈1.7 CPU-h) | **reproduces Goto–Ohno**; replay, tree check, all 1 625 rows recomputed |
| **10^9** | **7 881** | **4 143** | **37 018 s (10.3 h, 4 threads)** | **replay, tree check, all 4 143 rows recomputed against all 50 847 533 odd primes ≤ 10^9 (≈2.1·10^11 pairs, 0 mismatches)** |

The run took 10.3 h on an Apple M1 Pro laptop. For comparison, Goto and Ohno report about 26 000 CPU-hours
(2006–08) for the key lemma of their 10^8 proof.

**Certificate checksums** are in `SHA256SUMS`:
- `runs/rows_1000000000.txt`: `48980c9b…340b`
- `runs/c_1000000000.log`: `a2ac58d6…b542`

The checker outputs are:
- `runs/replay_1e9.out`
- `review/runs/verify_chain_1e9.out`, which contains the full row verification and the tree check
- `review/runs/rv_1e9_*.out`, the per-row details

## Method in one paragraph

Goto and Ohno classify the cyclotomic values Φ_r(p) for *all* primes p < 10^8. This program does not.

It runs a depth-first search that decides, prime by prime, whether a prime divides N and with which exponent.
Cyclotomic data (the admissible exponents of a prime p) is computed *lazily*, only for primes the search actually
reaches. That is about 4 100 primes at B = 10^9, instead of all 50.8 million.

Every pruning step is a necessary condition, decided in exact integer arithmetic:
- p-adic valuations of σ;
- lower and upper bounds on the abundancy σ(N)/N.

The full soundness argument is in [Soundness](#soundness).

## Repository layout

| path | what it is |
|---|---|
| `lpf.c` | the search (C, GMP, pthreads). `./lpf B kn/kd odd\|even threads rowsfile logfile` |
| `closure_solver.py` | original Python prototype; its event logs match `lpf.c` exactly at 10^4 and 10^6 |
| `replay.py` | **checker 1**: re-runs the search from the log in exact rational arithmetic (`Fraction`), re-multiplies every σ(p^a) factorisation, and computes its own rigorous bound M |
| `review/tree_check.py` | **checker 2**: written from scratch. It does not search. It reads the log as a proof tree and checks every node locally: branching covers all cases, every rejected exponent is impossible, every leaf satisfies its bound |
| `review/rowverify.c` | **checker 3**: recomputes **every** row independently. It uses its own prime source (primesieve), its own factorisation of q−1, its own order algorithm, its own Wieferich test and its own rigorous size bounds |
| `review/mup_check.c` | independent rigorous upper bound for M = ∏_{p ≤ B odd prime} p/(p−1) |
| `review/lpf_exact.c` | variant of `lpf.c` with the only floating-point filter replaced by integer arithmetic; identical output at 10^6 and 10^7 |
| `rows_check.py`, `rows_check_big.py` | earlier sampled row re-computations (numpy) |
| `planted_tests.py`, `mp_check.py`, `odd_control.py`, `control_check.py` | positive controls |
| `review/mutation-tests/` | corrupted inputs that the checkers must reject |
| `runs/`, `review/runs/` | all certificates and checker outputs |

## Reproduce

Needs a C compiler, GMP, primesieve and Python 3 with `numpy` and `sympy`.

```sh
make                     # builds lpf and the review tools
make check-small         # B = 10^6 end to end in a few seconds: search, replay, tree check
make check-1e9-replay    # checksums + replay + tree check of the published 10^9 certificate (~minutes)
./run_1e9.sh 4           # full 10^9 search on 4 threads (~10 h)
review/run_rowverify_1e9.sh 6 400   # full row verification at 10^9 (~7 h on 6 threads)
```

## Soundness

Notation:
- P is the set of odd primes ≤ B.
- The "allowed" primes are P ∪ {2}.

For an odd perfect N with all prime factors ≤ B we have σ(N) = 2N. So σ(N) has only allowed prime factors, and
v₂(σ(N)) = 1.

### 1. Factorisation

σ(p^a) = ∏_{d | a+1, d > 1} Φ_d(p).

Every prime factor q of Φ_d(p) satisfies one of two things:
- ord_q(p) = d; or
- q | d. In this case q is the largest prime factor P(d) of d, and v_q(Φ_d(p)) = 1 when d > 2.

### 2. Exponent sets (Bang–Zsigmondy)

Φ_d(p) has a primitive prime q with ord_q(p) = d in these cases:
- for d ≥ 3, except p = 2, d = 6;
- for d = 2, unless p+1 is a power of 2.

If p^a ‖ N and d | a+1, this q divides 2N, so q is an odd prime ≤ B. Hence d ∈ {ord_q(p) : q ∈ P, q ≠ p}.
The Zsigmondy exceptions are added explicitly.

**Row of p.** `lpf.c` computes ord_q(p) for every q ∈ P \ {p}. Each q − 1 is factored from a sieve table, and the
order uses Montgomery arithmetic.

**Good d.** d is "good" iff Φ_d(p) factors completely over the allowed primes. This is decided exactly:
1. Φ_d(p) is computed with GMP.
2. It is divided by every q with ord_q(p) = d, and by P(d).
3. By fact 1, these are the only allowed primes that can divide it. So the quotient is 1 iff Φ_d(p) is smooth over
   the allowed primes.

**Admissible a.** a is admissible iff every divisor e > 1 of a+1 is good. The admissible list is complete, so
there is no exponent cap.

**Size filter.** This filter only ever rejects, never accepts. Φ_d(p) > (p−1)^φ(d). So if

  Σ_{q: ord_q(p)=d} v_q·log q + log P(d) < φ(d)·log(p−1) − 1,

then Φ_d(p) is not smooth. The test uses a margin of 1, against rounding errors below 10^-3. `review/lpf_exact.c`
replaces it with integer arithmetic and produces identical output.

**Large orders.** For orders o above a threshold, the bucket {q : ord_q(p) = o} has at most ⌊(B−1)/o⌋ primes,
each with v_q = 1 unless the Wieferich-type test p^o ≡ 1 (mod q²) fires.
- When ⌊(B−1)/o⌋·log B + log o + 1 < φ(o)·log(p−1), o is rejected without storing the bucket.
- Otherwise the bucket is rebuilt exactly, and also whenever the Wieferich test fires.

### 3. Search tree

A node records:
- assigned primes, with their exponents;
- excluded primes;
- *required* primes: odd primes ≤ B that divide some assigned σ(p^a), so they must divide N.

**Branching.**
- If required primes exist, the largest one is branched over its complete admissible exponent list.
- Otherwise, the smallest undecided prime p ∈ P is either included or excluded.

**Pruning.** Every rule is a necessary condition:
- *Valuations.*
  - For an excluded odd q, v_q(∏σ) must be 0.
  - For an assigned q, v_q(∏σ) must be ≤ a_q.
  - For q = 2, it must be ≤ 1.
  - This also forces Euler's form: one odd exponent, with p ≡ a ≡ 1 (mod 4).
- *Exponent lower bound.* a_r ≥ the accumulated v_r.
- *Lower bound.* σ(N)/N ≥ A·∏_{required}(1 + 1/r). If this is > 2, the node is impossible.
- *Upper bound.* σ(N)/N < A·M/E, with E = ∏_{assigned ∪ excluded} p/(p−1). If this is < 2, the node is impossible.
  - M ≥ ∏_{p ∈ P} p/(p−1) is a rigorous bound, computed in two independent ways (`replay.py`, `review/mup_check.c`).
  - All comparisons are exact.

A node with no required primes and A = 2 would be a solution. The positive controls confirm that this path works.

### 4. Arithmetic limits

B < 2^31, so q² < 2^62 in the 64-bit Wieferich test.

## Verification layers

**Positive controls.** The same program, run on targets that do have solutions, finds them:
- all 3-perfect (6) and 4-perfect (30 of 36) numbers that are 10^5-smooth;
- all 1000-smooth 5-perfect (19) and 300-smooth 6-perfect (12) numbers in OEIS;
- 30 planted rational targets σ(N)/N = r, checked against brute force over odd 100-smooth N ≤ 10^8.

**Checker 1: `replay.py`.**
- Exact replay of the whole log.
- Recomputes all 20 677 σ(p^a) factorisations at 10^9.
- A tampered log or rows file is detected.

**Checker 2: `review/tree_check.py`.**
- A local proof-tree check, with M taken from `mup_check.c`.
- Corrupted logs and rows are rejected (see `review/mutation-tests/`).

**Checker 3: `review/rowverify.c`.**
- At 10^8, all 1 625 rows are recomputed.
- At 10^9, all 4 143 rows are recomputed.
- 0 mismatching rows.

**Reproduction of Goto–Ohno.** B = 10^8 gives no solutions, consistent with their theorem.

## Literature

- T. Goto, Y. Ohno, *Odd perfect numbers have a prime factor exceeding 10^8*, Math. Comp. 77 (2008) 1859–1868.
- P. Ochem, M. Rao, *Odd perfect numbers are greater than 10^1500*, Math. Comp. 81 (2012) 1869–1877.
- J. Zelinsky, *Upper bounds on the second largest prime factor of an odd perfect number*, Int. J. Number Theory (2019); arXiv:1810.13063.

## License

Code: MIT (see `LICENSE`). Data and certificates: CC BY 4.0.
