# H4 (Erdos 672, 3-term AP, fifth powers): Kummer route in Z[zeta_5]

Reduction (accepted locally): H4 <= Denes(5): x^5+y^5=2z^5 => x=y or z=0, and Ribet(5,3): x^5+y^5=8z^5 => z=0.
Unified view: a nontrivial H4 solution is a rational point (m/b^2, d/b^5) on Y^2 = 1 - X^5 with X,Y != 0.

## Steps (Lean files in this folder)
1. DONE  Zeta5.lean: K5, zeta, 1+z+z^2+z^3+z^4=0, z^5=1, golden ratio phi=1+z+z^4, phi^2=phi+1, phi unit, (2phi-1)^2=5. PID instance (Mathlib five_pid).
2. DONE  Coordinates: every element of O_K = a0 + a1 z + a2 z^2 + a3 z^3 uniquely (integralPowerBasis, dim 4).
3. DONE (core) lambda = 1 - z: lambda^4 = unit * 5; O/lambda = F_5; every alpha = c (mod lambda) with c in Z; alpha^5 = c^5 (mod lambda^5).
4. DONE (two_prime, zeta_not_fifth_mod_two) 2 is prime (inert): O/2 = F_16.
5. DONE (unit_form in Zeta5.lean) Units: every unit = zeta^k * (real unit); real units of Z[phi] are +-phi^m (descent on a + b phi).
6. DONE (kummer_lemma, mod lambda^3 suffices) Kummer lemma for p=5: a unit congruent to a rational integer mod lambda^5 is a fifth power (finite check on phi^m mod 5).
7. Denes case lambda does not divide z: x + zeta y = unit * alpha^5 for each conjugate; compare mod lambda^5.
8. Denes case lambda | z: descent on v_lambda(z) as in Mathlib FLT/Three.lean.
9. Same for 8 z^5 (2 | x+y with v_2 = 3).
10. Assemble with the reduction file into a full proof of H4.

## Denes 1952 (Acta Math. 88, 241-251), read 2026-11-27
Satz 7 (c = p1^u1...ps^us, all f_i even, sum 1/f_i <= (l-3)/(2(l-1)), some p_j^(l-1) != 1 mod l^2) and
Satz 9 (c = 2): x^l + y^l = c z^l, xyz != 0,1, unsolvable. For l = 5, p = 2: f = 4 (even), 1/4 <= 1/4,
2^4 = 16 != 1 mod 25. Since c = 8 = 2^3 is also a power of 2, Satz 7 covers BOTH H4 equations.
Proof (Satz 4) splits into three cases:
 a) 5 does not divide x y z: Satz 1, ideal descent using 5th power residue symbols, the unit
    Theta_1 (rank 1 for l = 5), and Vandiver's 1931 congruence rho_i = rho_{l-i} mod l^(l-1).
 b) 5 | y: Satz 3/6: x + zeta y = eps rho^5 forces zeta to be a 5th power mod each prime q | c.
    For q = (2) (inert, residue field F_16, order 15): zeta has order 5, not a 5th power. Finite check.
 c) 5 | z: Maillet's lemma (Acta Math. 24, 1901, 247-256), not yet obtained.
Dependencies still to source: Vandiver PNAS 17 (1931) 661-673; Maillet Acta Math 24 (1901).

## Maillet 1901 (Acta Math. 24, 247-256), lemma = Denes case c (5 | z), read 2026-11-27
Lemme: u^l + v^l = E (1-a)^(mu l - beta) A w^l impossible (u, v, w coprime to each other and to l,
A coprime to l with at most l-3 prime factors; for l = 5 and A = 2 or 8: one prime, ok).
Proof (about 1.5 pages): descent on mu. Choose two factors u + a^r v, u + a^s v not divisible by A's primes,
each = (1-a) e t^l. Eliminate via the 3x3 determinant to get t_r^l - eps t_s^l = E1 A (1-a)^(mu l - l - beta) w1^l.
Then eps is congruent to a rational integer mod a high power of (1-a), so by KUMMER'S LEMMA eps = eps'^l,
giving the same equation with mu - 1; mu = 1 is impossible by valuation count.
Needed: Kummer's lemma for l = 5 (unit = rational integer mod lambda^5 => 5th power): finite check on
zeta^k phi^m, using the unit classification of step 5.

## Vandiver 1931 (PNAS 17, 661-673), read 2026-11-27
Pages 664-665: for the equation theta^l + omega^l + delta gamma^l = 0 over Q(zeta + zeta^-1), from
(theta + omega zeta^a)/(1 +- zeta^a) = eta_a sigma_a^l and power characters {E_n / P} = 1 (n = 1..(l-3)/2),
"by taking the known expressions for power characters of units ... after some transformations" one gets
sigma_1 = sigma_-1 (mod lambda^(l-1)). That is the congruence Denes cites as (18). The derivation itself is
deferred to Vandiver, Trans. AMS 31 (1929) 613-642, p. 633 (footnote 4a), not yet obtained.
For l = 5 there is a single unit E_1 (rank 1); the congruence may be checkable directly for this case.
