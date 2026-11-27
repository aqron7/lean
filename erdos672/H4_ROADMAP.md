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
7. OPEN (case a) Denes case 5 does not divide xyz: x + zeta y = unit * alpha^5 for each conjugate; compare mod lambda^5.
8. DONE case b (5 | y): Zeta5.case_b. DONE case c (5 | z): Zeta5.maillet + Zeta5.case_c, any 2^j.
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

## Dirichlet 1825/1828 (Werke I, 21-46; archive.org werkehrsgaufvera01lejeuoft), read 2026-11-27
Thm VIII: x^5 +- y^5 = 5^n A z^5 impossible (n != 0, 2; A not divisible by 2, 5, or any prime 10k+1).
Thm IX: x^5 +- y^5 = A z^5 impossible for A (same restrictions) = 3,4,9,12,13,16,21,22 mod 25.
A must be ODD in VIII/IX, so A = 2 and A = 8 are NOT covered (consistent with Denes 1952 being the source
for c = 2). Dirichlet's elementary route does not bypass case a.
Status of case a (5 does not divide xyz): Denes Satz 1 needs Vandiver's rho_1 = rho_4 (mod lambda^4), derived
from power characters of units = Kummer's explicit reciprocity formula. This is the remaining hard core.
Note: the trivial solution x = y = z = 1 lies in case a, so case a cannot be settled by congruences alone.

## Case a analysis (2026-11-27)
Kummer first-case step (provable with existing Zeta5 lemmas): x + zeta y = zeta^3 phi^m alpha^5 and x = y (mod 5).
Three-term relation (zeta^4 - zeta)(x+y) + (1 - zeta^4)(x + zeta y) + (zeta - 1)(x + zeta^4 y) = 0 gives
alpha^5 + (sigma alpha)^5 = -2 phi^(1-m) a^5, a in Z (x + y = 2a^5, resp. 8a^5). This is the same equation over O
with a non-fifth-power unit, and closing the descent needs that unit to be a fifth power: exactly where Denes
uses Vandiver's congruence (explicit reciprocity for 5th power residue symbols). Not available in Mathlib.
Alternative: x^5 + y^5 = 2z^5 is equivalent to rational points on the genus 2 curve w^2 = 5s(s^5 + 8)
(s = (x+y)/z). A rank-0 Jacobian proof would need a 2-descent over Q(2^(1/5)) (its unit group), also large.

## Case a: real-family descent and the exact missing congruence (2026-11-27, scripts in casea/)
Family F_R: X^5 + Y^5 = 2^j eps Z^5, X, Y, Z in Z[phi] coprime, lambda not dividing XYZ (contains the integer case).
- Mod 2: X/Y mod 2 lies in F4 and must be a 5th root of 1, so 2 | X + Y and X + zeta Y = X*lambda (mod 2).
  F4* is inside (F16*)^5, so the unit zeta^k phi^m is congruent to lambda mod 5th powers in F16. No reciprocity needed.
- Mod lambda^5 (ex2.py, all X, Y mod 5 sqrt5): the pairs (1,4) and (2,3) are BOTH consistent only for k1 = 3, k2 = 1,
  so x + zeta y = zeta^3 phi^m rho^5 holds for real X, Y too.
- Three-term relation: rho^5 + (sigma rho)^5 = 2^j eps' W^5 with eps' real (family F').
- F' back to F_R: B_i = rho + zeta^i sigma rho, zeta^2 B_1 and zeta^3 B_4 real, giving R1^5 + delta R4^5 = 2^j eps'' R0^5.
  Need delta to be a 5th power. ex5.py: v_lambda(rho - sigma rho) is 1 or >= 3, and delta is a 5th power EXACTLY when
  v >= 3. Multiplying rho by zeta^a can always make v >= 3, but it also moves which B_i is divisible by 2.
- So the whole of case a reduces to ONE compatibility statement (Vandiver's congruence for l = 5):
  with gamma = rho / sigma rho, the 5th roots of unity that gamma is congruent to mod 2 and mod lambda^2 coincide.
  CRT shows this is independent of all local data, so it needs a global reciprocity law (it uses that x + zeta^2 y
  is also a unit times a 5th power). Candidates: Eisenstein reciprocity plus Kummer's supplementary law for l = 5,
  or the Hilbert symbol product formula. Vandiver, Trans. AMS 31 (1929) 613-642, p. 633 has the derivation;
  ams.org is behind a Cloudflare check, so it has to be uploaded manually.

## Case a: COMPLETE PROOF PLAN (2026-11-27). Only Eisenstein reciprocity for the integer 2 is needed.
Family F_R(j): X^5 + Y^5 = 2^j eps Z^5, X, Y real (sigma-fixed) in O, coprime, lambda not dividing Z, j in {1,3}.
Claim T: every F_R solution has X + zeta Y a unit (then X = Y = unit, so j = 1 and the integer solution is x = y).
Strong induction on absNorm(Z).
S1  2 | X + Y (2 prime; if 2 | X + zeta^i Y with i != 0 then by sigma 2 | Y). Factors X + zeta^i Y pairwise coprime,
    odd for i != 0: X + zeta^i Y = unit * 5th power, X + Y = 2^j e0 W^5, W | Z, and W strictly divides Z if rho_1 is not a unit.
S2  Mod lambda^5: X zeta-coefficients force units zeta^3 r1 (pair 1,4) and zeta^1 r2 (pair 2,3), r_i real
    (X s_k + Y s_{k-1} = 0 mod lambda^5, s_j = zeta^j - zeta^-j; compare the real units s_{k-1}/s_k mod 5).
S3  For each prime P | rho_1, in the finite field O/P with k = (q-1)/5:
    pairs a=2 and a=3 give psi(phi)^k = 1 (so psi(real unit)^k = 1), a=2 gives psi(Y(1-zeta))^k = 1,
    a=0 gives psi(2)^(jk) = 1, so psi(2)^k = 1: 2 is a 5th power mod P. Pure algebra in F_q^*.
S4  Degree 1: P | X + zeta Y with X, Y real implies zeta = integer mod P (Frobenius on F_p(phi)).
S5  Eisenstein for 2 (eis.py: 386/386): P = ker(psi), psi to ZMod p, pi a primary generator, psi(2)^k = 1, so pi^3 = 1 mod 2.
    Proof: J = jacobiSum chi chi. (i) J = chi(1/2)^2 mod 2 (involution t <-> 1-t). (ii) J = -1 mod lambda^2 (Mathlib).
    (iii) J in P and in tau_2^-1 P (power sums of degree < p-1 vanish). (iv) J * conj J = p (Mathlib), so
    J = w * pi * tau_3(pi) with w a primary unit, w = +-phi^n. Then (pi/2) = (2/P) using tau_3 (zeta^u -> zeta^3u).
S6  Good(x): primary normalization of x has cube = 1 mod 2. Multiplicative; true for units and for the primes in S5.
    So rho' = zeta^a rho_1 (primary) satisfies rho'^3 = 1 mod 2, hence sigma rho' = rho' mod 2 (sigma x = x^4 mod 2).
S7  Three-term relation: rho'^5 + (sigma rho')^5 = 2^j eps' W^5. B_i = rho' + zeta^i sigma rho', 2 | B_0, zeta^2 B_1 and
    zeta^3 B_4 real = real unit * real 5th power. zeta B_4 - B_1 = (zeta - 1)(rho' - sigma rho') is in lambda^3, so
    u4/u1 = rational mod lambda^3, Kummer lemma: u4/u1 = eta^5 with eta real. New solution (R1, eta R4, R0), R0 | W.
S8  Backward: if the new solution is trivial (B_0 = 2 u0, B_1, B_4 units) then u1 + u4 = -2 phi u0, i.e. v + w = 2 in
    units of Z[phi]: v in {1, phi, phi^-1, phi^2, phi^-2, -phi^-1}; integrality of rho' = u0((1+zeta)v - 2 zeta)/lambda
    forces v = 1 mod lambda, so v = 1 and rho' = u0 is a unit (back.py), contradiction.
