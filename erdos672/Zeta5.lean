import Mathlib

/-! Foundations for `ℤ[ζ₅]` (Kummer route to `x⁵ + y⁵ = 2z⁵`), step 1.
The cyclotomic relation, the golden-ratio unit `φ = 1 + ζ + ζ⁴`, and the integral power basis. -/

open NumberField

namespace OMA672Z5

/-- The fifth cyclotomic field. -/
abbrev K5 := CyclotomicField 5 ℚ

instance oma_ne5 : NeZero ((5 : ℕ) : ℚ) := ⟨by norm_num⟩

instance oma_cyc5 : IsCyclotomicExtension {5} ℚ K5 := CyclotomicField.isCyclotomicExtension 5 ℚ

instance oma_pid5 : IsPrincipalIdealRing (𝓞 K5) := IsCyclotomicExtension.Rat.five_pid K5

lemma hζ5 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 5 ℚ K5) 5 :=
  IsCyclotomicExtension.zeta_spec 5 ℚ K5

/-- `ζ` as an algebraic integer. -/
noncomputable abbrev ζ : 𝓞 K5 := hζ5.toInteger

lemma ζ_pow_five : ζ ^ 5 = 1 := hζ5.toInteger_isPrimitiveRoot.pow_eq_one

/-- `1 + ζ + ζ² + ζ³ + ζ⁴ = 0`. -/
lemma cyc : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
  have h := hζ5.toInteger_isPrimitiveRoot.geom_sum_eq_zero (by norm_num : 1 < 5)
  simpa [Finset.sum_range_succ, add_assoc] using h

lemma ζ_ne_one : ζ ≠ 1 := hζ5.toInteger_isPrimitiveRoot.ne_one (by norm_num)

/-- The golden ratio `φ = 1 + ζ + ζ⁴ = (1 + √5)/2`. -/
noncomputable abbrev φ : 𝓞 K5 := 1 + ζ + ζ ^ 4

lemma φ_sq : φ ^ 2 = φ + 1 := by
  linear_combination cyc + (ζ ^ 3 + 2) * ζ_pow_five

lemma φ_mul : φ * (φ - 1) = 1 := by linear_combination φ_sq

/-- `φ` is a unit. -/
lemma φ_isUnit : IsUnit φ := ⟨⟨φ, φ - 1, φ_mul, by rw [mul_comm]; exact φ_mul⟩, rfl⟩

/-- `√5 = 2φ - 1`. -/
lemma sqrt5_sq : (2 * φ - 1) ^ 2 = 5 := by linear_combination 4 * φ_sq

/-- Every element of `𝓞 K5` has integer coordinates in `1, ζ, ζ², ζ³`. -/
lemma exists_coord (x : 𝓞 K5) : ∃ a b c e : ℤ, x = a + b * ζ + c * ζ ^ 2 + e * ζ ^ 3 := by
  obtain ⟨f, rfl⟩ := hζ5.integralPowerBasis.exists_eq_aeval' x
  rw [IsPrimitiveRoot.integralPowerBasis_gen]
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, b, c, e, h1⟩ := hp
    obtain ⟨a', b', c', e', h2⟩ := hq
    exact ⟨a + a', b + b', c + c', e + e', by rw [map_add, h1, h2]; push_cast; ring⟩
  | monomial n r =>
    rw [Polynomial.aeval_monomial]
    induction n with
    | zero => exact ⟨r, 0, 0, 0, by simp⟩
    | succ n ih =>
      obtain ⟨a, b, c, e, h⟩ := ih
      refine ⟨-e, a - e, b - e, c - e, ?_⟩
      rw [pow_succ, ← mul_assoc, h]
      push_cast
      linear_combination (e : 𝓞 K5) * cyc

/-- Coordinates are unique. -/
lemma coord_zero {a b c e : ℤ} (h : (a : 𝓞 K5) + b * ζ + c * ζ ^ 2 + e * ζ ^ 3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  have hdim : hζ5.integralPowerBasis.dim = 4 := by
    rw [IsPrimitiveRoot.integralPowerBasis_dim, Nat.totient_prime Nat.prime_five]
  let B := hζ5.integralPowerBasis.basis.reindex (finCongr hdim)
  have hB : ∀ i : Fin 4, B i = ζ ^ (i : ℕ) := by
    intro i
    simp [B, Module.Basis.reindex_apply, PowerBasis.coe_basis, IsPrimitiveRoot.integralPowerBasis_gen]
  have key := (Fintype.linearIndependent_iff.mp B.linearIndependent) ![a, b, c, e] (by
    simp [Fin.sum_univ_four, hB, Matrix.vecHead, Matrix.vecTail, zsmul_eq_mul]
    linear_combination h)
  exact ⟨key 0, key 1, key 2, key 3⟩

lemma coord_eq {a b c e a' b' c' e' : ℤ}
    (h : (a : 𝓞 K5) + b * ζ + c * ζ ^ 2 + e * ζ ^ 3 = a' + b' * ζ + c' * ζ ^ 2 + e' * ζ ^ 3) :
    a = a' ∧ b = b' ∧ c = c' ∧ e = e' := by
  have := coord_zero (a := a - a') (b := b - b') (c := c - c') (e := e - e')
    (by push_cast; linear_combination h)
  omega

/-- `λ = 1 - ζ`, the prime above 5. -/
noncomputable abbrev lam : 𝓞 K5 := 1 - ζ

/-- The unit cofactor in `5 = λ⁴ u`. -/
noncomputable abbrev u5 : 𝓞 K5 := (1 + ζ) * (1 + ζ + ζ ^ 2) * (1 + ζ + ζ ^ 2 + ζ ^ 3)

lemma five_eq : lam ^ 4 * u5 = 5 := by
  linear_combination (ζ ^ 6 - 2 * ζ ^ 5 + ζ ^ 3 + 3 * ζ - 4) * cyc

lemma lam_pow_four_dvd_five : lam ^ 4 ∣ (5 : 𝓞 K5) := ⟨u5, five_eq.symm⟩

/-- Every element is congruent to a rational integer modulo `λ`. -/
lemma exists_int_congr (x : 𝓞 K5) : ∃ c : ℤ, lam ∣ x - c := by
  obtain ⟨a, b, c, e, rfl⟩ := exists_coord x
  refine ⟨a + b + c + e, -(b + c * (1 + ζ) + e * (1 + ζ + ζ ^ 2)), ?_⟩
  push_cast; ring

/-- If `α ≡ c (mod λ)` then `α⁵ ≡ c⁵ (mod λ⁵)`. -/
lemma pow_five_congr {α : 𝓞 K5} {c : ℤ} (h : lam ∣ α - c) : lam ^ 5 ∣ α ^ 5 - (c : 𝓞 K5) ^ 5 := by
  obtain ⟨β, hβ⟩ := h
  have hα : α = c + lam * β := by linear_combination hβ
  refine ⟨c ^ 4 * u5 * β + 2 * c ^ 3 * u5 * lam * β ^ 2 + 2 * c ^ 2 * u5 * lam ^ 2 * β ^ 3
    + c * u5 * lam ^ 3 * β ^ 4 + β ^ 5, ?_⟩
  rw [hα]
  linear_combination (-(c : 𝓞 K5) ^ 4 * lam * β - 2 * (c : 𝓞 K5) ^ 3 * lam ^ 2 * β ^ 2
    - 2 * (c : 𝓞 K5) ^ 2 * lam ^ 3 * β ^ 3 - (c : 𝓞 K5) * lam ^ 4 * β ^ 4) * five_eq

end OMA672Z5
