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

end OMA672Z5
