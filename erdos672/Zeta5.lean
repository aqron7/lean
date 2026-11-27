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

section Conj

open NumberField.IsCMField

instance oma_cm5 : NumberField.IsCMField K5 :=
  IsCyclotomicExtension.Rat.isCMField K5 (S := {5}) ⟨5, rfl, by norm_num⟩

/-- `ζ` as a unit. -/
noncomputable abbrev ζu : (𝓞 K5)ˣ := (hζ5.toInteger_isPrimitiveRoot.isUnit (by norm_num)).unit

lemma ζu_torsion : ζu ∈ NumberField.Units.torsion K5 :=
  (CommGroup.mem_torsion _).mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨5, by norm_num, by ext; simp [ζ_pow_five]⟩)

/-- Complex conjugation on `𝓞 K5`. -/
noncomputable abbrev σ := ringOfIntegersComplexConj K5

lemma σ_ζ : σ ζ = ζ ^ 4 := by
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj]
  have h : complexConj K5 (ζ : K5) = (ζ : K5)⁻¹ := complexConj_torsion K5 ⟨ζu, ζu_torsion⟩
  rw [h]
  have h5 : (ζ : K5) ^ 5 = 1 := by exact_mod_cast congrArg (fun x : 𝓞 K5 => (x : K5)) ζ_pow_five
  have hne : (ζ : K5) ≠ 0 := by rintro h0; rw [h0] at h5; norm_num at h5
  push_cast
  field_simp
  linear_combination -h5

/-- `5` is not a unit, via coordinates. -/
lemma five_not_dvd_one : ¬ (5 : 𝓞 K5) ∣ 1 := by
  rintro ⟨v, hv⟩
  obtain ⟨a, b, c, e, rfl⟩ := exists_coord v
  have := coord_eq (a := 1) (b := 0) (c := 0) (e := 0) (a' := 5 * a) (b' := 5 * b) (c' := 5 * c)
    (e' := 5 * e) (by push_cast; linear_combination hv)
  omega

lemma lam_not_dvd_one : ¬ lam ∣ 1 := by
  rintro ⟨t, ht⟩
  obtain ⟨a, b, c, e, rfl⟩ := exists_coord t
  have := coord_eq (a := 1) (b := 0) (c := 0) (e := 0) (a' := a + e) (b' := b - a + e)
    (c' := c - b + e) (e' := 2 * e - c) (by push_cast; rw [ht]; linear_combination (-(e : 𝓞 K5)) * cyc)
  omega

lemma lam_dvd_int {m : ℤ} (h : lam ∣ (m : 𝓞 K5)) : (5 : ℤ) ∣ m := by
  by_contra h5
  have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  obtain ⟨a, b, hab⟩ := ((Prime.coprime_iff_not_dvd hp).mpr h5).symm
  apply lam_not_dvd_one
  have : (1 : 𝓞 K5) = a * m + b * 5 := by exact_mod_cast hab.symm
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_right
    (dvd_trans (dvd_pow_self lam (by norm_num)) lam_pow_four_dvd_five) _)

end Conj

section RealUnits

open NumberField.IsCMField

/-- `φ = -ζ² - ζ³`. -/
lemma φ_eq : φ = -ζ ^ 2 - ζ ^ 3 := by linear_combination cyc

/-- Real elements (fixed by conjugation) are `a + c φ`. -/
lemma real_form {w : 𝓞 K5} (hw : σ w = w) : ∃ a c : ℤ, w = a + c * φ := by
  obtain ⟨a, b, c, e, rfl⟩ := exists_coord w
  have h1 : σ ((a : 𝓞 K5) + b * ζ + c * ζ ^ 2 + e * ζ ^ 3)
      = ((a - b : ℤ) : 𝓞 K5) + ((-b : ℤ) : 𝓞 K5) * ζ + ((e - b : ℤ) : 𝓞 K5) * ζ ^ 2
        + ((c - b : ℤ) : 𝓞 K5) * ζ ^ 3 := by
    simp only [map_add, map_mul, map_pow, map_intCast, σ_ζ]
    push_cast
    linear_combination (b : 𝓞 K5) * cyc + ((c : 𝓞 K5) * ζ ^ 3 + e * ζ ^ 7 + e * ζ ^ 2) * ζ_pow_five
  rw [h1] at hw
  have := coord_eq hw
  obtain ⟨-, hb, -, hce⟩ := this
  refine ⟨a, -c, ?_⟩
  have hb0 : b = 0 := by omega
  have hec : e = c := by omega
  subst hb0; subst hec
  rw [φ_eq]; push_cast; ring

/-- Coordinates in `1, φ` are unique. -/
lemma φcoord_eq {x y x' y' : ℤ} (h : (x : 𝓞 K5) + y * φ = x' + y' * φ) : x = x' ∧ y = y' := by
  rw [φ_eq] at h
  have := coord_eq (a := x) (b := 0) (c := -y) (e := -y) (a' := x') (b' := 0) (c' := -y')
    (e' := -y') (by push_cast; linear_combination h)
  omega

/-- A real unit has norm `±1` in `ℤ[φ]`. -/
lemma real_unit_norm {a c a' c' : ℤ} (h : ((a : 𝓞 K5) + c * φ) * (a' + c' * φ) = 1) :
    a ^ 2 + a * c - c ^ 2 = 1 ∨ a ^ 2 + a * c - c ^ 2 = -1 := by
  have e : ((a * a' + c * c' : ℤ) : 𝓞 K5) + ((a * c' + a' * c + c * c' : ℤ) : 𝓞 K5) * φ
      = ((1 : ℤ) : 𝓞 K5) + ((0 : ℤ) : 𝓞 K5) * φ := by
    push_cast; rw [← h]; linear_combination (-(c : 𝓞 K5) * c') * φ_sq
  obtain ⟨h1, h2⟩ := φcoord_eq e
  have hn : (a ^ 2 + a * c - c ^ 2) * (a' ^ 2 + a' * c' - c' ^ 2) = 1 := by
    have : (a ^ 2 + a * c - c ^ 2) * (a' ^ 2 + a' * c' - c' ^ 2)
        = (a * a' + c * c') ^ 2 + (a * a' + c * c') * (a * c' + a' * c + c * c')
          - (a * c' + a' * c + c * c') ^ 2 := by ring
    rw [this, h1, h2]; ring
  exact Int.eq_one_or_neg_one_of_mul_eq_one hn

end RealUnits

section UnitDecomp

open NumberField.IsCMField

lemma σ_lam_dvd (x : 𝓞 K5) (h : lam ∣ x) : lam ∣ σ x := by
  obtain ⟨t, rfl⟩ := h
  rw [map_mul]
  apply dvd_mul_of_dvd_left
  have : σ lam = lam * (1 + ζ + ζ ^ 2 + ζ ^ 3) := by
    simp only [lam, map_sub, map_one, σ_ζ]; ring
  rw [this]; exact dvd_mul_right _ _

lemma coe_unitsComplexConj (u : (𝓞 K5)ˣ) : ((unitsComplexConj K5 u : (𝓞 K5)ˣ) : 𝓞 K5) = σ u := by
  apply RingOfIntegers.ext; rfl

/-- Every unit is `ζ^k` times a real element. -/
lemma unit_decomp (u : (𝓞 K5)ˣ) : ∃ k : ℕ, ∃ w : 𝓞 K5, (u : 𝓞 K5) = ζ ^ k * w ∧ σ w = w := by
  set t := unitsMulComplexConjInv K5 u with htdef
  have ht : ((t : (𝓞 K5)ˣ) : 𝓞 K5) * σ u = u := by
    rw [htdef, unitsMulComplexConjInv_apply, Units.val_mul, ← coe_unitsComplexConj, mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hfin : IsOfFinOrder ((((t : (𝓞 K5)ˣ) : 𝓞 K5) : K5)) := by
    have h1 : IsOfFinOrder (t : (𝓞 K5)ˣ) := (CommGroup.mem_torsion _).mp t.2
    exact MonoidHom.isOfFinOrder ((algebraMap (𝓞 K5) K5 : 𝓞 K5 →* K5).comp (Units.coeHom (𝓞 K5))) h1
  obtain ⟨r, -, hr⟩ := IsPrimitiveRoot.exists_pow_or_neg_mul_pow_of_isOfFinOrder
    (by decide : Odd 5) hζ5 hfin
  have hz : ((ζ : 𝓞 K5) : K5) = IsCyclotomicExtension.zeta 5 ℚ K5 := rfl
  have hr' : ((t : (𝓞 K5)ˣ) : 𝓞 K5) = ζ ^ r ∨ ((t : (𝓞 K5)ˣ) : 𝓞 K5) = -ζ ^ r := by
    rcases hr with h | h
    · left; apply RingOfIntegers.ext; exact h
    · right; apply RingOfIntegers.ext; simp only [map_neg, map_pow]; exact h
  have h5 : ∀ n : ℕ, ζ ^ (5 * n) = 1 := fun n => by rw [pow_mul, ζ_pow_five, one_pow]
  refine ⟨3 * r, ζ ^ (4 * (3 * r)) * u, ?_, ?_⟩
  · rw [← mul_assoc, ← pow_add, show 3 * r + 4 * (3 * r) = 5 * (3 * r) by ring, h5, one_mul]
  · have hσw : σ (ζ ^ (4 * (3 * r)) * u) = ζ ^ (48 * r) * σ u := by
      rw [map_mul, map_pow, σ_ζ, ← pow_mul]; ring_nf
    rw [hσw]
    rcases hr' with h | h
    · conv_rhs => rw [← ht, h]
      rw [show 48 * r = 4 * (3 * r) + r + 5 * (7 * r) by ring, pow_add, h5, mul_one, pow_add]
      ring
    · exfalso
      -- σ w = -w for w = ζ^(12r) u
      set w := ζ ^ (4 * (3 * r)) * u with hw
      have hσ : σ w = -w := by
        rw [hw, hσw]
        conv_rhs => rw [← ht, h]
        rw [show 48 * r = 4 * (3 * r) + r + 5 * (7 * r) by ring, pow_add, h5, mul_one, pow_add]
        ring
      have hwu : IsUnit w := by
        rw [hw]; exact (IsUnit.pow _ (hζ5.toInteger_isPrimitiveRoot.isUnit (by norm_num))).mul u.isUnit
      obtain ⟨c, hc⟩ := exists_int_congr w
      have h2 : lam ∣ σ (w - c) := σ_lam_dvd _ hc
      rw [map_sub, map_intCast, hσ] at h2
      have h3 : lam ∣ ((-2 * c : ℤ) : 𝓞 K5) := by
        have := dvd_add hc h2; push_cast; convert this using 1; ring
      have h4 := lam_dvd_int h3
      have h5c : (5 : ℤ) ∣ c := by
        have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
        rcases hp.dvd_or_dvd (show (5 : ℤ) ∣ (-2) * c from h4) with h | h
        · norm_num at h
        · exact h
      have hlc : lam ∣ (c : 𝓞 K5) := by
        obtain ⟨k, hk⟩ := h5c
        rw [hk]; push_cast
        exact dvd_mul_of_dvd_left (dvd_trans (dvd_pow_self lam (by norm_num)) lam_pow_four_dvd_five) _
      have hlw : lam ∣ w := by have := dvd_add hc hlc; simpa using this
      apply lam_not_dvd_one
      obtain ⟨v, hv⟩ := hwu
      rw [← hv] at hlw
      exact dvd_trans hlw ⟨↑v⁻¹, by simp⟩

end UnitDecomp

end OMA672Z5
