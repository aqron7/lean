import Mathlib

/-! Lemma L (Euler): if `gcd(s, 3t) = 1`, `s + t` is odd and `s ^ 2 + 3 t ^ 2` is a cube, then
`s + t √-3 = (u + v √-3) ^ 3` for integers `u, v`. Proved in the Eisenstein integers. -/

open NumberField IsCyclotomicExtension.Rat.Three

namespace OMA672

local notation "K3" => CyclotomicField 3 ℚ

instance oma_ne3 : NeZero ((3 : ℕ) : ℚ) := ⟨by norm_num⟩

instance oma_cyc3 : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

attribute [local instance] IsCyclotomicExtension.Rat.three_pid

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

end OMA672
