# Erdos 307, variant coprime_one_notMem: search log

Solver: `s307c.c` (gcc -O2 s307c.c -lm; usage `./s307c <max elt> <max size> [start]`).
Checks every pairwise coprime P with elements in [2, B] and |P| <= K; Q unrestricted.

Pruning (all necessary conditions):
1. S_P * S_Q = 1 where S_X = sum 1/x.
2. S_Q <= sum of 1/p over primes p | N = sigma(P), and those primes are coprime to prod(P).
   omega(N) is capped by N's size, so S_Q <= sum of 1/p over the smallest primes coprime to
   prod(P) whose product is <= N. Applied at every node of the enumeration with a global bound on N.
3. Parity: P all odd needs |P| even; sigma(P) odd needs an even number of Q blocks.
4. Partition DFS with an upper bound on the reciprocal sum of the blocks.

Validation: with start=1 it reproduces the original s307.c output exactly (B=60 K=5, B=40 K=6),
including Cambie's examples. Candidate counts match the u128 version on overlapping ranges.

Note: original s307.c silently skipped P with sigma(P) >= 2^62 or more than 14 prime powers.

## Ruled out (no P survives even the H-bound filter)
| max size K | max element B |
|---|---|
| 3 | 10^12 |
| 4 | 10^12 |
| 5 | 10^9 |
| 6 | 10^8 |
| 7 | 10^7 |
| 8 | 10^6 |
| 9 | 3*10^5 |
| 10 | 10^5 |
| 11 | 3*10^4 |
| 12 | 10^4 |
| 14 | 3000 |
| 16 | 1000 |
| 18 | 400 |
| 20 | 250 |

K=24 at B=150 and K=28 at B=100 did not finish in 300s.
