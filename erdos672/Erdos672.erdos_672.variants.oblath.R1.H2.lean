import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1
import Mathlib

-- Step Erdos672.erdos_672.variants.oblath.R1.H2: hypothesis H2 of reduction Erdos672.erdos_672.variants.oblath.R1
-- Credit: @aqron7

/-! Lemma L (Euler): if `gcd(s, 3t) = 1`, `s + t` is odd and `s ^ 2 + 3 t ^ 2` is a cube, then
`s + t √-3 = (u + v √-3) ^ 3` for integers `u, v`. Proved in the Eisenstein integers. -/

open NumberField IsCyclotomicExtension.Rat.Three

namespace OMA672

/-- The third cyclotomic field. -/
abbrev K3 := CyclotomicField 3 ℚ

instance oma_ne3 : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance oma_cyc3 : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

instance oma_pid : IsPrincipalIdealRing (𝓞 K3) := IsCyclotomicExtension.Rat.three_pid K3

lemma hζ3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K3) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K3

/-- The Eisenstein unit `ω`. -/
noncomputable abbrev ω : 𝓞 K3 := hζ3.toInteger

lemma ω_sq : ω ^ 2 = -ω - 1 := eta_sq hζ3

lemma ω_cube : ω ^ 3 = 1 := hζ3.toInteger_cube_eq_one

/-- Integer coordinates in the basis `1, ω` are unique. -/
lemma coord_zero {a b : ℤ} (h : (a : 𝓞 K3) + b * ω = 0) : a = 0 ∧ b = 0 := by
  have hn : ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K3) = 0 := by
    have : ((a ^ 2 - a * b + b ^ 2 : ℤ) : 𝓞 K3) = ((a : 𝓞 K3) + b * ω) * (a + b * ω ^ 2) := by
      push_cast
      linear_combination (-(b : 𝓞 K3) ^ 2 * ω - (a : 𝓞 K3) * b + (b : 𝓞 K3) ^ 2) * ω_sq
    rw [this, h, zero_mul]
  have hz : a ^ 2 - a * b + b ^ 2 = 0 := by exact_mod_cast hn
  constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

lemma coord_eq {a b c d : ℤ} (h : (a : 𝓞 K3) + b * ω = c + d * ω) : a = c ∧ b = d := by
  have := coord_zero (a := a - c) (b := b - d) (by push_cast; linear_combination h)
  omega

/-- Every element of `𝓞 K3` has integer coordinates. -/
lemma exists_coord (x : 𝓞 K3) : ∃ a b : ℤ, x = a + b * ω := by
  obtain ⟨f, rfl⟩ := hζ3.integralPowerBasis.exists_eq_aeval' x
  rw [IsPrimitiveRoot.integralPowerBasis_gen]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, b, ha⟩ := hp
    obtain ⟨c, d, hc⟩ := hq
    exact ⟨a + c, b + d, by rw [map_add, ha, hc]; push_cast; ring⟩
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    induction n with
    | zero => exact ⟨c, 0, by simp⟩
    | succ n ih =>
      obtain ⟨a, b, hab⟩ := ih
      refine ⟨-b, a - b, ?_⟩
      rw [pow_succ, ← mul_assoc, hab]
      push_cast
      linear_combination (b : 𝓞 K3) * ω_sq

/-- `√-3 = 1 + 2 ω`. -/
noncomputable abbrev r3 : 𝓞 K3 := 1 + 2 * ω

lemma r3_sq : r3 ^ 2 = -3 := by
  linear_combination 4 * ω_sq

theorem lemma_L {s t b : ℤ} (hc : IsCoprime s (3 * t)) (hpar : Odd (s + t))
    (hb : s ^ 2 + 3 * t ^ 2 = b ^ 3) :
    ∃ u v : ℤ, s = u ^ 3 - 9 * u * v ^ 2 ∧ t = 3 * u ^ 2 * v - 3 * v ^ 3 := by
  set ρ : 𝓞 K3 := s + t * r3 with hρ
  set ρ' : 𝓞 K3 := s - t * r3 with hρ'
  have hprod : ρ * ρ' = (b : 𝓞 K3) ^ 3 := by
    have : ((s ^ 2 + 3 * t ^ 2 : ℤ) : 𝓞 K3) = ((b ^ 3 : ℤ) : 𝓞 K3) := by rw [hb]
    push_cast at this
    rw [← this, hρ, hρ']
    linear_combination (-(t : 𝓞 K3) ^ 2) * r3_sq
  -- coprimality of ρ and ρ'
  have hcop : IsCoprime ρ ρ' := by
    have h3 : IsCoprime s 3 := hc.of_mul_right_left
    have ht : IsCoprime s t := hc.of_mul_right_right
    have hA : IsCoprime (s ^ 2 + 3 * t ^ 2) s := by
      have : IsCoprime (3 * t ^ 2) s := (h3.mul_right ht.pow_right).symm
      have e : s ^ 2 + 3 * t ^ 2 = 3 * t ^ 2 + s * s := by ring
      rw [e]; exact this.add_mul_left_left s
    have hB : IsCoprime (s ^ 2 + 3 * t ^ 2) 2 := by
      obtain ⟨k, hk⟩ := hpar
      refine ⟨1, -(2 * k ^ 2 + 2 * k - 2 * k * t - t + 2 * t ^ 2), ?_⟩
      have : s = 2 * k + 1 - t := by omega
      rw [this]; ring
    obtain ⟨A, B, hAB⟩ := hA.mul_right hB
    refine ⟨A * ρ' + B, B, ?_⟩
    have : ((A * (s ^ 2 + 3 * t ^ 2) + B * (s * 2) : ℤ) : 𝓞 K3) = 1 := by rw [hAB]; simp
    push_cast at this
    rw [← this, hρ, hρ']
    linear_combination (-(A : 𝓞 K3) * (t : 𝓞 K3) ^ 2) * r3_sq
  obtain ⟨γ0, u0, hu0⟩ := exists_associated_pow_of_mul_eq_pow' hcop hprod
  -- ρ = ± ω ^ k * γ0 ^ 3
  have hunit : ∃ k ∈ ({0, 1, 2} : Finset ℕ), ∃ γ1 : 𝓞 K3, ρ = ω ^ k * γ1 ^ 3 := by
    have hm := Units.mem hζ3 u0
    have e : ((IsPrimitiveRoot.isUnit (hζ3.toInteger_isPrimitiveRoot) (by decide)).unit :
      𝓞 K3) = ω := rfl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with h | h | h | h | h | h <;> subst h
    · exact ⟨0, by simp, γ0, by rw [← hu0]; simp⟩
    · exact ⟨0, by simp, -γ0, by rw [← hu0]; simp; ring⟩
    · exact ⟨1, by simp, γ0, by rw [← hu0]; simp [e]; ring⟩
    · exact ⟨1, by simp, -γ0, by rw [← hu0]; simp [e]; ring⟩
    · exact ⟨2, by simp, γ0, by rw [← hu0]; simp [e]; ring⟩
    · exact ⟨2, by simp, -γ0, by rw [← hu0]; simp [e]; ring⟩
  obtain ⟨k, hk, γ1, hγ1⟩ := hunit
  -- normalise γ1 to have even ω-coordinate
  obtain ⟨c, d, hcd⟩ := exists_coord γ1
  have hnorm : ∃ u v : ℤ, γ1 ^ 3 = (u + v * r3) ^ 3 := by
    rcases Int.even_or_odd d with ⟨v, hv⟩ | hd
    · exact ⟨c - v, v, by rw [hcd, hv]; push_cast; ring⟩
    · rcases Int.even_or_odd c with ⟨w, hw⟩ | hco
      · -- ω^2 γ1 = (d - c) + (-c) ω, and -c is even
        refine ⟨d - c + w, -w, ?_⟩
        have : γ1 ^ 3 = (ω ^ 2 * γ1) ^ 3 := by
          rw [mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ω_cube]; ring
        rw [this, hcd, hw]
        push_cast
        have e2 : ω ^ 2 * ((c : 𝓞 K3) + d * ω) = (d - c) + (-c) * ω := by
          linear_combination (c : 𝓞 K3) * ω_sq + (d : 𝓞 K3) * ω_cube
        rw [hw] at e2; push_cast at e2
        rw [e2]; ring
      · -- ω γ1 = -d + (c - d) ω, and c - d is even
        obtain ⟨w, hw⟩ : Even (c - d) := by
          rcases hco with ⟨i, hi⟩; rcases hd with ⟨j, hj⟩; exact ⟨i - j, by omega⟩
        refine ⟨-d - w, w, ?_⟩
        have : γ1 ^ 3 = (ω * γ1) ^ 3 := by rw [mul_pow, ω_cube, one_mul]
        rw [this, hcd]
        have e1 : ω * ((c : 𝓞 K3) + d * ω) = -d + ((c - d : ℤ) : 𝓞 K3) * ω := by
          push_cast; linear_combination (d : 𝓞 K3) * ω_sq
        rw [e1, hw]; push_cast; ring
  obtain ⟨u, v, huv⟩ := hnorm
  rw [huv] at hγ1
  set P := u ^ 3 - 9 * u * v ^ 2 with hP
  set Q := 3 * u ^ 2 * v - 3 * v ^ 3 with hQ
  have hcube : ((u : 𝓞 K3) + v * r3) ^ 3 = P + Q * r3 := by
    rw [hP, hQ]; push_cast
    linear_combination (3 * (u : 𝓞 K3) * v ^ 2 + (v : 𝓞 K3) ^ 3 * r3) * r3_sq
  rw [hcube] at hγ1
  -- compare coordinates in each case
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · refine ⟨u, v, ?_⟩
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((P + Q : ℤ) : 𝓞 K3) + ((2 * Q : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1
    have := coord_eq h0
    constructor <;> omega
  · exfalso
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((-2 * Q : ℤ) : 𝓞 K3) + ((P - Q : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1 + 2 * (Q : 𝓞 K3) * ω_sq
    have := coord_eq h0
    obtain ⟨k, hk⟩ := hpar
    omega
  · exfalso
    have h0 : ((s + t : ℤ) : 𝓞 K3) + ((2 * t : ℤ) : 𝓞 K3) * ω
        = ((Q - P : ℤ) : 𝓞 K3) + ((-(P + Q) : ℤ) : 𝓞 K3) * ω := by
      push_cast; linear_combination hγ1 + ((P : 𝓞 K3) + Q) * ω_sq + 2 * (Q : 𝓞 K3) * ω_cube
    have := coord_eq h0
    obtain ⟨k, hk⟩ := hpar
    omega

/-- If `u ^ 3 - 9 u v ^ 2 + 3 u ^ 2 v - 3 v ^ 3` is odd then `u + v` is odd. -/
lemma odd_add_of_odd_PQ {u v : ℤ}
    (h : Odd (u ^ 3 - 9 * u * v ^ 2 + (3 * u ^ 2 * v - 3 * v ^ 3))) : Odd (u + v) := by
  rcases Int.even_or_odd (u + v) with ⟨m, hm⟩ | ho
  · exfalso
    have hu : u = 2 * m - v := by omega
    rw [← Int.not_even_iff_odd] at h
    apply h
    exact ⟨4 * m ^ 3 - 12 * m * v ^ 2 + 4 * v ^ 3, by rw [hu]; ring⟩
  · exact ho

lemma isCoprime_two_of_odd {n : ℤ} (h : Odd n) : IsCoprime n 2 := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨1, -k, by ring⟩

lemma cube_left {a b c : ℤ} (h : IsCoprime a b) (habc : a * b = c ^ 3) : ∃ d, a = d ^ 3 :=
  Int.eq_pow_of_mul_eq_pow_odd_left h (by decide) habc

lemma natAbs_le_of_mul {a b : ℤ} (hb : b ≠ 0) : a.natAbs ≤ (a * b).natAbs := by
  rw [Int.natAbs_mul]
  exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hb)

theorem euler_aux (n : ℕ) : ∀ x y z : ℤ, z.natAbs = n → x ^ 3 + y ^ 3 = 2 * z ^ 3 → x ≠ y →
    z ≠ 0 → False := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn h hxy hz
  have ih' : ∀ a b c : ℤ, a ^ 3 + b ^ 3 = 2 * c ^ 3 → a ≠ b → c ≠ 0 →
      c.natAbs < z.natAbs → False :=
    fun a b c h1 h2 h3 h4 => ih _ (hn ▸ h4) a b c rfl h1 h2 h3
  clear ih hn
  -- Step A: x and y coprime
  have hcop : IsCoprime x y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpz : (p : ℤ) ∣ z := by
      have h3 : (p : ℤ) ^ 3 ∣ 2 * z ^ 3 := ⟨x1 ^ 3 + y1 ^ 3, by rw [← h]; ring⟩
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpp.dvd_or_dvd (dvd_trans (dvd_pow_self _ (by norm_num)) h3) with h2 | h2
      · -- p ∣ 2, so p = 2
        have hp2 : p = 2 := by
          have : p ∣ 2 := by exact_mod_cast h2
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
        subst hp2
        obtain ⟨k, hk⟩ := h3
        push_cast at hk ⊢
        have : (2 : ℤ) ∣ z ^ 3 := ⟨2 * k, by linarith⟩
        exact Int.prime_two.dvd_of_dvd_pow this
      · exact hpp.dvd_of_dvd_pow h2
    obtain ⟨z1, rfl⟩ := hpz
    have h1 : x1 ^ 3 + y1 ^ 3 = 2 * z1 ^ 3 := by
      have hp3 : (p : ℤ) ^ 3 ≠ 0 := pow_ne_zero _ hp0
      apply mul_left_cancel₀ hp3
      linear_combination h
    apply ih' x1 y1 z1 h1 (fun e => hxy (by rw [e])) (fun e => hz (by rw [e, mul_zero]))
    have hz1 : z1.natAbs ≠ 0 := by
      intro h0; apply hz; simp [Int.natAbs_eq_zero.mp h0]
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_left (Nat.pos_of_ne_zero hz1) hp.one_lt
  -- Step B: x, y odd; write x = s + t, y = s - t
  have hxy_even : Even (x + y) := by
    have h2 : Even (x ^ 3 + y ^ 3) := ⟨z ^ 3, by rw [h]; ring⟩
    rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at h2
    rw [Int.even_add]; exact h2
  obtain ⟨s, hs⟩ := hxy_even
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := by
        obtain ⟨r, hr⟩ := hx
        exact ⟨s - r, by omega⟩
      have h2 := Int.isCoprime_iff_gcd_eq_one.mp hcop
      have : (2 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hx.two_dvd hy.two_dvd
      rw [h2] at this; norm_num at this
    · exact hx
  set t := x - s with ht
  have hx' : x = s + t := by omega
  have hy' : y = s - t := by omega
  have hpar : Odd (s + t) := by rw [← hx']; exact hxodd
  have ht0 : t ≠ 0 := by intro h0; apply hxy; omega
  have heq : s * (s ^ 2 + 3 * t ^ 2) = z ^ 3 := by
    have : (s + t) ^ 3 + (s - t) ^ 3 = 2 * z ^ 3 := by rw [← hx', ← hy']; exact h
    linarith [this]
  have hs0 : s ≠ 0 := by
    intro h0; apply hz; rw [h0, zero_mul] at heq; exact pow_eq_zero_iff (by norm_num) |>.mp heq.symm
  have hst : IsCoprime s t := by
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a + b, a - b, by rw [← hab, hx', hy']; ring⟩
  have hM3 : 3 ≤ (s ^ 2 + 3 * t ^ 2).natAbs := by
    have : 0 < t ^ 2 := by positivity
    have : 3 ≤ s ^ 2 + 3 * t ^ 2 := by nlinarith [sq_nonneg s]
    omega
  by_cases h3s : (3 : ℤ) ∣ s
  · -- Case 2: 3 ∣ s
    obtain ⟨s', rfl⟩ := h3s
    have h3t : IsCoprime t 3 := by
      rw [isCoprime_comm, Prime.coprime_iff_not_dvd Int.prime_three]
      intro h3; exact Int.prime_three.not_isUnit (hst.isUnit_of_dvd' (dvd_mul_right 3 s') h3)
    have hs't : IsCoprime s' t := hst.of_mul_left_right
    have h3z : (3 : ℤ) ∣ z := by
      apply Int.prime_three.dvd_of_dvd_pow (n := 3)
      exact ⟨s' * (9 * s' ^ 2 + 3 * t ^ 2), by rw [← heq]; ring⟩
    obtain ⟨w, rfl⟩ := h3z
    set M := t ^ 2 + 3 * s' ^ 2 with hM
    have hw : s' * M = 3 * w ^ 3 := by
      have : 27 * (s' * M) = 27 * (3 * w ^ 3) := by rw [hM]; linear_combination 3 * heq
      linarith
    have hM3' : ¬ (3 : ℤ) ∣ M := by
      intro h3
      have : (3 : ℤ) ∣ t ^ 2 := by
        have := dvd_sub h3 (dvd_mul_right 3 (s' ^ 2)); rwa [hM, add_sub_cancel_right] at this
      have := Int.prime_three.dvd_of_dvd_pow this
      exact Int.prime_three.not_isUnit (h3t.isUnit_of_dvd' this (dvd_refl 3))
    have h3s' : (3 : ℤ) ∣ s' := by
      rcases Int.prime_three.dvd_or_dvd (⟨w ^ 3, hw⟩ : (3 : ℤ) ∣ s' * M) with h | h
      · exact h
      · exact absurd h hM3'
    obtain ⟨s'', rfl⟩ := h3s'
    have hw' : s'' * M = w ^ 3 := by linarith [hw]
    have hs''M : IsCoprime s'' M := by
      have : IsCoprime s'' t := hs't.of_mul_left_right
      have h1 : IsCoprime s'' (t ^ 2) := this.pow_right
      have e : M = t ^ 2 + s'' * (27 * s'') := by rw [hM]; ring
      rw [e]; exact h1.add_mul_left_right _
    obtain ⟨c, hc⟩ := cube_left hs''M hw'
    obtain ⟨b, hb⟩ := cube_left hs''M.symm (by rw [mul_comm]; exact hw')
    have hL1 : IsCoprime t (3 * (3 * s'')) := h3t.mul_right hs't.symm
    have hL2 : Odd (t + 3 * s'') := by
      have : t + 3 * s'' = 3 * (3 * s'') + t - 2 * (3 * s'') := by ring
      rw [this]
      obtain ⟨k, hk⟩ := hpar
      exact ⟨k - 3 * s'', by omega⟩
    obtain ⟨u, v, hu, hv⟩ := lemma_L hL1 hL2 (by have := hb; rw [hM] at this; exact this)
    have hvc : v * ((u - v) * (u + v)) = c ^ 3 := by
      rw [← hc]
      have : 3 * (v * ((u - v) * (u + v))) = 3 * s'' := by linear_combination -hv
      omega
    have huv : IsCoprime u v := by
      have h1 : IsCoprime t (3 * s'') := hs't.symm
      rw [hu, hv] at h1
      have e1 : u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) := by ring
      have e2 : 3 * u ^ 2 * v - 3 * v ^ 3 = v * (3 * u ^ 2 - 3 * v ^ 2) := by ring
      rw [e1, e2] at h1
      exact h1.of_mul_left_left.of_mul_right_left
    have hodd : Odd (u + v) := by
      have h1 := hL2
      rw [hu, hv] at h1
      exact odd_add_of_odd_PQ h1
    have hvm : IsCoprime v (u - v) := by
      have e : u - v = u + v * (-1) := by ring
      rw [e]; exact huv.symm.add_mul_left_right _
    have hvp : IsCoprime v (u + v) := by
      have e : u + v = u + v * 1 := by ring
      rw [e]; exact huv.symm.add_mul_left_right _
    have hmp : IsCoprime (u - v) (u + v) := by
      have h2 : IsCoprime (u - v) 2 := isCoprime_two_of_odd (by
        obtain ⟨k, hk⟩ := hodd; exact ⟨k - v, by omega⟩)
      have h2v : IsCoprime (u - v) (2 * v) := h2.mul_right hvm.symm
      have e : u + v = 2 * v + (u - v) * 1 := by ring
      rw [e]; exact h2v.add_mul_left_right _
    obtain ⟨γ, hγ⟩ := cube_left (hvm.mul_right hvp) hvc
    obtain ⟨α, hα⟩ := cube_left (hmp.mul_right hvm.symm) (by rw [← hvc]; ring)
    obtain ⟨β, hβ⟩ := cube_left (hmp.symm.mul_right hvp.symm) (by rw [← hvc]; ring)
    have hv0 : v ≠ 0 := by
      intro h0; apply hs0; rw [h0] at hv; linarith [hv]
    have hu0 : u ≠ 0 := by
      intro h0; apply ht0; rw [hu, h0]; ring
    have hγ0 : γ ≠ 0 := by rintro rfl; apply hv0; rw [hγ]; ring
    apply ih' β (-α) γ (by linear_combination -hβ + hα + 2 * hγ) ?_ hγ0 ?_
    · intro e
      apply hu0
      have : β ^ 3 = -(α ^ 3) := by rw [e]; ring
      linarith [hα, hβ, this]
    · -- |γ| ≤ |c| ≤ |w| < 3 |w| = |z|
      have hc0 : c ≠ 0 := by
        rintro rfl; apply hs0; rw [hc]; ring
      have hγc : γ.natAbs ^ 3 ≤ c.natAbs ^ 3 := by
        rw [← Int.natAbs_pow, ← Int.natAbs_pow, ← hγ, ← hvc]
        have hm : (u - v) * (u + v) ≠ 0 := by
          intro h0; apply hc0; have := hvc; rw [h0, mul_zero] at this
          exact pow_eq_zero_iff (by norm_num) |>.mp this.symm
        exact natAbs_le_of_mul hm
      have hγc' : γ.natAbs ≤ c.natAbs :=
        (Nat.pow_le_pow_iff_left (by norm_num)).mp hγc
      have hb0 : b ≠ 0 := by
        rintro rfl; have : M = 0 := by rw [hb]; ring
        rw [hM] at this; nlinarith [sq_pos_of_ne_zero ht0, sq_nonneg s'']
      have hwcb : w ^ 3 = (c * b) ^ 3 := by rw [mul_pow, ← hc, ← hb, hw']
      have hw : w.natAbs = c.natAbs * b.natAbs := by
        rw [← Int.natAbs_mul]
        have := congrArg Int.natAbs hwcb
        rw [Int.natAbs_pow, Int.natAbs_pow] at this
        exact Nat.pow_left_injective (by norm_num) this
      have hb1 : 1 ≤ b.natAbs := Int.natAbs_pos.mpr hb0
      rw [Int.natAbs_mul]
      norm_num
      nlinarith [Int.natAbs_pos.mpr hc0]
  · -- Case 1: 3 ∤ s
    have h3 : IsCoprime s 3 := by
      rw [isCoprime_comm, Prime.coprime_iff_not_dvd Int.prime_three]; exact h3s
    have hL1 : IsCoprime s (3 * t) := h3.mul_right hst
    have hsM : IsCoprime s (s ^ 2 + 3 * t ^ 2) := by
      have : IsCoprime s (3 * t ^ 2) := h3.mul_right hst.pow_right
      have e : s ^ 2 + 3 * t ^ 2 = 3 * t ^ 2 + s * s := by ring
      rw [e]; exact this.add_mul_left_right _
    obtain ⟨a, ha⟩ := cube_left hsM heq
    obtain ⟨b, hb⟩ := cube_left hsM.symm (by rw [mul_comm]; exact heq)
    obtain ⟨u, v, hu, hv⟩ := lemma_L hL1 hpar hb
    have huv : IsCoprime u v := by
      have h1 := hst
      rw [hu, hv] at h1
      have e1 : u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) := by ring
      have e2 : 3 * u ^ 2 * v - 3 * v ^ 3 = v * (3 * u ^ 2 - 3 * v ^ 2) := by ring
      rw [e1, e2] at h1
      exact h1.of_mul_left_left.of_mul_right_left
    have hu3 : IsCoprime u 3 := by
      have h1 := h3
      rw [hu, show u ^ 3 - 9 * u * v ^ 2 = u * (u ^ 2 - 9 * v ^ 2) by ring] at h1
      exact h1.of_mul_left_left
    have hodd : Odd (u + v) := by
      apply odd_add_of_odd_PQ; rw [← hu, ← hv]; exact hpar
    have hsfac : s = u * ((u - 3 * v) * (u + 3 * v)) := by rw [hu]; ring
    have hu3v : IsCoprime u (3 * v) := hu3.mul_right huv
    have hum : IsCoprime u (u - 3 * v) := by
      have e : u - 3 * v = -(3 * v) + u * 1 := by ring
      rw [e]; exact hu3v.neg_right.add_mul_left_right _
    have hup : IsCoprime u (u + 3 * v) := by
      have e : u + 3 * v = 3 * v + u * 1 := by ring
      rw [e]; exact hu3v.add_mul_left_right _
    have hmp : IsCoprime (u - 3 * v) (u + 3 * v) := by
      have h2 : IsCoprime (u - 3 * v) 2 := isCoprime_two_of_odd (by
        obtain ⟨k, hk⟩ := hodd; exact ⟨k - 2 * v, by omega⟩)
      have h3' : IsCoprime (u - 3 * v) 3 := by
        have e : u - 3 * v = u + 3 * (-v) := by ring
        rw [e]; exact (hu3.symm.add_mul_left_right _).symm
      have hv' : IsCoprime (u - 3 * v) v := by
        have e : u - 3 * v = u + v * (-3) := by ring
        rw [e]; exact (huv.symm.add_mul_left_right _).symm
      have h6 : IsCoprime (u - 3 * v) (6 * v) := by
        have := (h2.mul_right h3').mul_right hv'
        convert this using 2; ring
      have e : u + 3 * v = 6 * v + (u - 3 * v) * 1 := by ring
      rw [e]; exact h6.add_mul_left_right _
    rw [hsfac] at ha
    obtain ⟨α, hα⟩ := cube_left (hum.mul_right hup) ha
    obtain ⟨β, hβ⟩ := cube_left (hmp.mul_right hum.symm) (by rw [← ha]; ring)
    obtain ⟨γ, hγ⟩ := cube_left (hmp.symm.mul_right hup.symm) (by rw [← ha]; ring)
    have hu0 : u ≠ 0 := by intro h0; apply hs0; rw [hsfac, h0, zero_mul]
    have hv0 : v ≠ 0 := by intro h0; apply ht0; rw [hv, h0]; ring
    have hα0 : α ≠ 0 := by rintro rfl; apply hu0; rw [hα]; ring
    apply ih' β γ α (by linear_combination -hβ - hγ + 2 * hα) ?_ hα0 ?_
    · intro e; apply hv0
      have : β ^ 3 = γ ^ 3 := by rw [e]
      linarith [hβ, hγ, this]
    · -- |α|^3 = |u| ≤ |s| < |z|^3
      have hm : (u - 3 * v) * (u + 3 * v) ≠ 0 := by
        intro h0; apply hs0; rw [hsfac, h0, mul_zero]
      have h1 : α.natAbs ^ 3 ≤ s.natAbs := by
        rw [← Int.natAbs_pow, ← hα, hsfac]; exact natAbs_le_of_mul hm
      have h2 : z.natAbs ^ 3 = s.natAbs * (s ^ 2 + 3 * t ^ 2).natAbs := by
        rw [← Int.natAbs_pow, ← heq, Int.natAbs_mul]
      have hs1 : 1 ≤ s.natAbs := Int.natAbs_pos.mpr hs0
      have h3' : α.natAbs ^ 3 < z.natAbs ^ 3 := by rw [h2]; nlinarith
      exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp h3'

/-- Euler: `x ^ 3 + y ^ 3 = 2 z ^ 3` forces `x = y` or `z = 0`. -/
theorem euler_cubes (x y z : ℤ) (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : x = y ∨ z = 0 := by
  by_contra hc
  push_neg at hc
  exact euler_aux _ x y z rfl h hc.1 hc.2

end OMA672

namespace OMA672

/-- Euler: the only integer solutions of `x ^ 3 + y ^ 3 = 2 z ^ 3` have `x = y` or `z = 0`. -/
def EulerCubes : Prop := ∀ x y z : ℤ, x ^ 3 + y ^ 3 = 2 * z ^ 3 → x = y ∨ z = 0

lemma cube_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (habc : a * b = c ^ 3) : ∃ u, a = u ^ 3 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) habc

/-- If `E * O = 2 * m ^ 3` with `E` even and `E, O` coprime then `E = 2 u ^ 3`, `O = w ^ 3`. -/
lemma split_even {E O m : ℕ} (hc : Nat.Coprime E O) (hE : Even E) (h : E * O = 2 * m ^ 3) :
    ∃ u w, E = 2 * u ^ 3 ∧ O = w ^ 3 := by
  obtain ⟨E', rfl⟩ := hE
  have h' : E' * O = m ^ 3 := by nlinarith [h]
  have hc' : Nat.Coprime E' O := Nat.Coprime.coprime_mul_left (by rwa [← two_mul] at hc)
  obtain ⟨u, hu⟩ := cube_of_coprime hc' h'
  obtain ⟨w, hw⟩ := cube_of_coprime hc'.symm (by rw [mul_comm]; exact h')
  exact ⟨u, w, by rw [hu]; ring, hw⟩

theorem ap3_ne_cube (core : EulerCubes) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) : n * ((n + d) * (n + 2 * d)) ≠ q ^ 3 := by
  intro hq
  have c1 : Nat.Coprime (n + d) n := by
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.Coprime.symm hnd
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := by
    have : n + 2 * d = (n + d) + d := by ring
    rw [this, Nat.coprime_self_add_right, Nat.coprime_add_self_left]; exact hnd
  have hmid : (n + d) * (n * (n + 2 * d)) = q ^ 3 := by rw [← hq]; ring
  obtain ⟨b, hb⟩ := cube_of_coprime (Nat.Coprime.mul_right c1 c2) hmid
  have hb0 : (b : ℤ) ≠ 0 := by
    intro h0; have : b = 0 := by exact_mod_cast h0
    subst this; simp at hb; omega
  rcases Nat.even_or_odd n with hev | hodd
  · -- n even: n = 2A, d odd, A and A + d coprime
    obtain ⟨A, hA⟩ := hev
    have hA' : n = 2 * A := by omega
    subst hA'
    have hdodd : Odd d := by
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | h
      · exfalso
        have : 2 ∣ Nat.gcd (2 * A) d := Nat.dvd_gcd ⟨A, rfl⟩ ⟨k, by omega⟩
        rw [hnd] at this; omega
      · exact h
    have hcAC : Nat.Coprime A (A + d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.coprime_mul_left hnd
    have hrest : 2 * A * (2 * A + 2 * d) = 4 * (A * (A + d)) := by ring
    have hBA : (2 * A * (2 * A + 2 * d)) * (2 * A + d) = q ^ 3 := by rw [← hmid]; ring
    obtain ⟨m, hm⟩ := cube_of_coprime (Nat.Coprime.mul_right c1 c2).symm hBA
    rw [hrest] at hm
    have hm2 : 2 ∣ m := by
      have : 2 ∣ m ^ 3 := ⟨2 * (A * (A + d)), by rw [← hm]; ring⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    obtain ⟨m', rfl⟩ := hm2
    have hAC : A * (A + d) = 2 * m' ^ 3 := by nlinarith [hm]
    have hsum : 2 * A + d = A + (A + d) := by ring
    have hApos : 0 < A := by omega
    rcases Nat.even_or_odd A with hAe | hAo
    · obtain ⟨u, w, hu, hw⟩ := split_even hcAC hAe hAC
      have key : (b : ℤ) ^ 3 + (-(w : ℤ)) ^ 3 = 2 * (u : ℤ) ^ 3 := by
        have : b ^ 3 = 2 * u ^ 3 + w ^ 3 := by rw [← hb, hsum, hw, hu]
        have : ((b ^ 3 : ℕ) : ℤ) = ((2 * u ^ 3 + w ^ 3 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      rcases core _ _ _ key with h | h
      · have hw0 : (0 : ℤ) < w := by
          have : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h0 | h0
            · subst h0; simp at hw; omega
            · exact h0
          exact_mod_cast this
        have : (0 : ℤ) ≤ b := by positivity
        omega
      · have : u = 0 := by exact_mod_cast h
        subst this; simp at hu; omega
    · have hCe : Even (A + d) := by
        rcases hAo with ⟨k, hk⟩; rcases hdodd with ⟨j, hj⟩; exact ⟨k + j + 1, by omega⟩
      obtain ⟨u, w, hu, hw⟩ := split_even hcAC.symm hCe (by rw [mul_comm]; exact hAC)
      have key : (b : ℤ) ^ 3 + (-(w : ℤ)) ^ 3 = 2 * (u : ℤ) ^ 3 := by
        have : b ^ 3 = 2 * u ^ 3 + w ^ 3 := by rw [← hb, hsum, hu, hw]; ring
        have : ((b ^ 3 : ℕ) : ℤ) = ((2 * u ^ 3 + w ^ 3 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      rcases core _ _ _ key with h | h
      · have hw0 : (0 : ℤ) < w := by
          have : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h0 | h0
            · subst h0; simp at hw; omega
            · exact h0
          exact_mod_cast this
        have : (0 : ℤ) ≤ b := by positivity
        omega
      · have : u = 0 := by exact_mod_cast h
        subst this; simp at hu; omega
  · -- n odd: the three terms are pairwise coprime cubes
    have c3 : Nat.Coprime n (n + 2 * d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.mul_right (hodd.coprime_two_right) hnd
    have hfirst : n * ((n + d) * (n + 2 * d)) = q ^ 3 := hq
    obtain ⟨a, ha⟩ := cube_of_coprime (Nat.Coprime.mul_right c1.symm c3) hfirst
    have hlast : (n + 2 * d) * (n * (n + d)) = q ^ 3 := by rw [← hq]; ring
    obtain ⟨c, hc⟩ := cube_of_coprime (Nat.Coprime.mul_right c3.symm c2.symm) hlast
    have key : (a : ℤ) ^ 3 + (c : ℤ) ^ 3 = 2 * (b : ℤ) ^ 3 := by
      have : a ^ 3 + c ^ 3 = 2 * b ^ 3 := by rw [← ha, ← hb, ← hc]; ring
      exact_mod_cast this
    rcases core _ _ _ key with h | h
    · have : a = c := by exact_mod_cast h
      subst this; omega
    · exact hb0 h


end OMA672

theorem OMA.solution : OMA.R_Erdos672_erdos_672_variants_oblath_R1.H2 := by
  show Erdos672.Erdos672With 3 3
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k <;> simp <;> omega
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by simp; omega
  have h2 : n + d ∉ ({n + 2 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton] at hq
  exact OMA672.ap3_ne_cube OMA672.euler_cubes hn hd hnd hq
