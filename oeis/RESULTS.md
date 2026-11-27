# lefttosolve.com OEIS existence problems: search log (no leases taken)

| Problem | Target | Searched | Result |
|---|---|---|---|
| OeisA113010.conjecture | n = (#digits)^(digit sum), n not 1, 32 | all digit counts d <= 3000 | none |
| OeisA109905.conjecture | a(n) = 0 beyond n = 1, 6, 30, 54 | n <= 200000 | none |
| OeisA108301.conjecture | digit sum of 2^2^n+1 prime, n > 11 | n = 12..23 | none |
| OeisA67599.conjecture | a(n) = n (factorization encoding p1 e1 p2 e2 ...) | brute n < 2e6; structured n = A*p, A < 1e9, p up to 2000 digits | none |

A67599 structure: if n = A*p with p the largest prime, exponent 1, L digits, then
p*(A-10) = enc(A)*10^(L+1) + 1. Requires enc(A) in (A/100, A/10]. Only 12 divisibility events for
A < 1e9 (A = 2187, 2401 families), none prime. A = 2401 gives an infinite family L = 136 mod 199
but any prime there has 136+ digits and cannot be certified in Lean without native_decide.
