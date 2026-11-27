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

section Golden

/-- Pairs `(a, c)` representing `±φ^m`. -/
inductive Reach : ℤ → ℤ → Prop
  | one : Reach 1 0
  | neg {a c} : Reach a c → Reach (-a) (-c)
  | mulφ {a c} : Reach a c → Reach c (a + c)
  | mulψ {a c} : Reach a c → Reach (c - a) a

lemma Reach.of_mulφ {a c : ℤ} (h : Reach c (a + c)) : Reach a c := by
  have := h.mulψ
  simpa using this

lemma Reach.of_mulψ {a c : ℤ} (h : Reach (c - a) a) : Reach a c := by
  have := h.mulφ
  simpa using this

theorem reach_of_norm (N : ℕ) : ∀ a c : ℤ, a.natAbs + c.natAbs = N →
    (a ^ 2 + a * c - c ^ 2 = 1 ∨ a ^ 2 + a * c - c ^ 2 = -1) → Reach a c := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a c hN hn
  rcases eq_or_ne c 0 with rfl | hc
  · have : a = 1 ∨ a = -1 := by
      rcases hn with h | h
      · have h2 : (a - 1) * (a + 1) = 0 := by linear_combination h
        rcases mul_eq_zero.mp h2 with h | h
        · left; linarith
        · right; linarith
      · nlinarith [sq_nonneg a]
    rcases this with rfl | rfl
    · exact Reach.one
    · exact Reach.one.neg
  rcases eq_or_ne a 0 with rfl | ha
  · -- c = ±1, and (0, ±1) = ±φ
    have : c = 1 ∨ c = -1 := by
      rcases hn with h | h
      · nlinarith [sq_nonneg c]
      · have h2 : (c - 1) * (c + 1) = 0 := by linear_combination -h
        rcases mul_eq_zero.mp h2 with h | h
        · left; linarith
        · right; linarith
    rcases this with rfl | rfl
    · exact Reach.one.mulφ |>.of_mulφ |>.mulφ
    · exact (Reach.one.mulφ).neg
  -- generic step
  rcases le_or_gt 0 (a * c) with hs | hs
  · -- same sign: multiply by φ⁻¹, new pair (c - a, a)
    apply Reach.of_mulψ
    apply ih ((c - a).natAbs + a.natAbs) _ (c - a) a rfl
    · rcases hn with h | h
      · right; linear_combination -h
      · left; linear_combination -h
    · rw [← hN]
      have hac : |c - a| < |c| := by
        rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hc with hc' | hc'
        · rw [abs_lt]; constructor <;> [skip; skip] <;>
            rcases hn with h | h <;> nlinarith [abs_of_neg hc']
        · nlinarith
        · nlinarith
        · rw [abs_lt]; constructor <;> rcases hn with h | h <;> nlinarith [abs_of_pos hc']
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hac
      omega
  · -- opposite signs: multiply by φ, new pair (c, a + c)
    apply Reach.of_mulφ
    apply ih (c.natAbs + (a + c).natAbs) _ c (a + c) rfl
    · rcases hn with h | h
      · right; linear_combination -h
      · left; linear_combination -h
    · rw [← hN]
      have hac : |a + c| < |a| := by
        rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hc with hc' | hc'
        · nlinarith
        · rw [abs_lt]; constructor <;> rcases hn with h | h <;> nlinarith [abs_of_neg ha']
        · rw [abs_lt]; constructor <;> rcases hn with h | h <;> nlinarith [abs_of_pos ha']
        · nlinarith
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hac
      omega


/-- The golden unit `Φ`. -/
noncomputable abbrev Φ : (𝓞 K5)ˣ := φ_isUnit.unit

lemma Φ_inv : ((Φ⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = φ - 1 := Units.inv_eq_of_mul_eq_one_right φ_mul

lemma reach_val {a c : ℤ} (h : Reach a c) :
    ∃ m : ℤ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (a : 𝓞 K5) + c * φ = s * ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) := by
  induction h with
  | one => exact ⟨0, 1, Or.inl rfl, by simp⟩
  | neg _ ih =>
    obtain ⟨m, s, hs, he⟩ := ih
    refine ⟨m, -s, ?_, ?_⟩
    · rcases hs with rfl | rfl <;> simp
    · push_cast; linear_combination -he
  | mulφ _ ih =>
    obtain ⟨m, s, hs, he⟩ := ih
    refine ⟨m + 1, s, hs, ?_⟩
    rw [zpow_add_one, Units.val_mul, ← mul_assoc, ← he]
    push_cast
    show _ = _ * φ
    linear_combination -(↑_ : 𝓞 K5) * φ_sq
  | mulψ _ ih =>
    obtain ⟨m, s, hs, he⟩ := ih
    refine ⟨m - 1, s, hs, ?_⟩
    rw [zpow_sub_one, Units.val_mul, ← mul_assoc, ← he, Φ_inv]
    push_cast
    linear_combination (-(↑_ : 𝓞 K5)) * φ_sq

/-- Every unit of `ℤ[ζ₅]` is `±ζ^k φ^m`. -/
theorem unit_form (u : (𝓞 K5)ˣ) :
    ∃ k : ℕ, ∃ m : ℤ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (u : 𝓞 K5) = s * ζ ^ k * ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) := by
  obtain ⟨k, w, hu, hw⟩ := unit_decomp u
  set w' : 𝓞 K5 := ζ ^ k * ((u⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) with hw'
  have hww' : w * w' = 1 := by
    have h5 : ζ ^ (5 * k) = 1 := by rw [pow_mul, ζ_pow_five, one_pow]
    have : w = ζ ^ (4 * k) * u := by
      rw [hu, ← mul_assoc, ← pow_add, show 4 * k + k = 5 * k by ring, h5, one_mul]
    rw [hw', this]
    calc ζ ^ (4 * k) * (u : 𝓞 K5) * (ζ ^ k * ((u⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5))
        = ζ ^ (4 * k + k) * ((u : 𝓞 K5) * ((u⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) := by ring
      _ = 1 := by rw [show 4 * k + k = 5 * k by ring, h5, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, one_mul]
  have hw'r : σ w' = w' := by
    have h1 : σ w * σ w' = 1 := by rw [← map_mul, hww', map_one]
    rw [hw] at h1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hww'
    exact mul_left_cancel₀ hw0 (h1.trans hww'.symm)
  obtain ⟨a, c, rfl⟩ := real_form hw
  obtain ⟨a', c', hac'⟩ := real_form hw'r
  rw [hac'] at hww'
  have hn := real_unit_norm hww'
  have hr := reach_of_norm _ a c rfl hn
  obtain ⟨m, s, hs, he⟩ := reach_val hr
  exact ⟨k, m, s, hs, by rw [hu, he]; ring⟩

end Golden

section Kummer

/-- The unit `v` with `σ λ = λ v`. -/
noncomputable abbrev v5 : 𝓞 K5 := 1 + ζ + ζ ^ 2 + ζ ^ 3

lemma φ_eq_three : φ = 3 - v5 * lam ^ 2 := by
  linear_combination ζ_pow_five

lemma ζ_eq : ζ = 1 - lam := by ring

lemma one_sub_pow (k : ℕ) : ∃ P : 𝓞 K5,
    (1 - lam) ^ k = 1 - (k : 𝓞 K5) * lam + ((k * (k - 1) / 2 : ℕ) : 𝓞 K5) * lam ^ 2 + lam ^ 3 * P := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P * (1 - lam) - ((k * (k - 1) / 2 : ℕ) : 𝓞 K5), ?_⟩
    have hk : ((k + 1) * (k + 1 - 1) / 2 : ℕ) = (k * (k - 1) / 2 : ℕ) + k := by
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [show (j + j + 1) * (j + j + 1 - 1) = 2 * ((j + j + 1) * j) by
            rw [show j + j + 1 - 1 = j + j by omega]; ring,
          show (j + j) * (j + j - 1) = 2 * (j * (j + j - 1)) by ring]
        rw [Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp
        · have : j + j - 1 + 1 = j + j := by omega
          nlinarith [this]
      · rw [show (2 * j + 1 + 1) * (2 * j + 1 + 1 - 1) = 2 * ((j + 1) * (2 * j + 1)) by
            rw [show 2 * j + 1 + 1 - 1 = 2 * j + 1 by omega]; ring,
          show (2 * j + 1) * (2 * j + 1 - 1) = 2 * ((2 * j + 1) * j) by
            rw [show 2 * j + 1 - 1 = 2 * j by omega]; ring]
        rw [Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
        ring
    rw [pow_succ, hP, hk]
    push_cast
    ring

lemma three_sub_pow (r : ℕ) : ∃ Q : 𝓞 K5,
    (3 - v5 * lam ^ 2) ^ r = 3 ^ r - (r : 𝓞 K5) * 3 ^ (r - 1) * v5 * lam ^ 2 + lam ^ 3 * Q := by
  induction r with
  | zero => exact ⟨0, by simp⟩
  | succ r ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨Q * (3 - v5 * lam ^ 2) + (r : 𝓞 K5) * 3 ^ (r - 1) * v5 ^ 2 * lam, ?_⟩
    rw [pow_succ, hQ]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp; ring
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

lemma lam_ne_zero : lam ≠ 0 := by
  intro h
  have := five_eq
  rw [h] at this
  norm_num at this

lemma lam_pow_dvd_of_five_dvd {m : ℤ} (h : (5 : ℤ) ∣ m) {j : ℕ} (hj : j ≤ 4) :
    lam ^ j ∣ (m : 𝓞 K5) := by
  obtain ⟨t, rfl⟩ := h
  push_cast
  exact dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow lam hj) lam_pow_four_dvd_five) _

lemma five_dvd_of_lam_dvd_nat {m : ℕ} (h : lam ∣ (m : 𝓞 K5)) : 5 ∣ m := by
  have : (5 : ℤ) ∣ (m : ℤ) := lam_dvd_int (by exact_mod_cast h)
  exact_mod_cast this

lemma v5_congr : lam ∣ v5 - 4 := ⟨-(3 + 2 * ζ + ζ ^ 2), by ring⟩

/-- Cancel one factor of `λ`. -/
lemma lam_cancel {j : ℕ} {X : 𝓞 K5} (h : lam ^ (j + 1) ∣ lam * X) : lam ^ j ∣ X := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, mul_left_cancel₀ lam_ne_zero (by rw [ht]; ring)⟩

/-- Core of Kummer's lemma for `l = 5`. -/
theorem kummer_core {k r : ℕ} {n : ℤ} (h : lam ^ 3 ∣ ζ ^ k * φ ^ r - n) : 5 ∣ k ∧ 5 ∣ r := by
  obtain ⟨P, hP⟩ := one_sub_pow k
  obtain ⟨Q, hQ⟩ := three_sub_pow r
  set C : ℕ := k * (k - 1) / 2 with hCdef
  set A : 𝓞 K5 := ((3 ^ r - n : ℤ) : 𝓞 K5) with hA
  set Y : 𝓞 K5 := (C : 𝓞 K5) * 3 ^ r - (r : 𝓞 K5) * 3 ^ (r - 1) * v5 with hY
  set X : 𝓞 K5 := -(k : 𝓞 K5) * 3 ^ r + Y * lam with hX
  set R : 𝓞 K5 := P * (3 ^ r - (r : 𝓞 K5) * 3 ^ (r - 1) * v5 * lam ^ 2 + lam ^ 3 * Q)
        + (1 - (k : 𝓞 K5) * lam + (C : 𝓞 K5) * lam ^ 2) * Q
        + (k : 𝓞 K5) * (r : 𝓞 K5) * 3 ^ (r - 1) * v5
        - (C : 𝓞 K5) * (r : 𝓞 K5) * 3 ^ (r - 1) * v5 * lam with hR
  have hexp : ζ ^ k * φ ^ r - n = A + lam * X + lam ^ 3 * R := by
    rw [hA, hX, hY, hR, ζ_eq, φ_eq_three, hP, hQ]; push_cast; ring
  rw [hexp] at h
  have hAX : lam ^ 3 ∣ A + lam * X := by
    have := dvd_sub h (dvd_mul_right (lam ^ 3) R); convert this using 1; ring
  -- 5 ∣ 3^r - n
  have hA1 : lam ∣ A := by
    have h1 := dvd_trans (dvd_pow_self lam (by norm_num)) hAX
    have := dvd_sub h1 (dvd_mul_right lam X); convert this using 1; ring
  have hA3 : lam ^ 3 ∣ A := lam_pow_dvd_of_five_dvd (lam_dvd_int hA1) (by norm_num)
  have hX2 : lam ^ 2 ∣ X := lam_cancel (by have := dvd_sub hAX hA3; convert this using 1; ring)
  -- 5 ∣ k
  have hk : 5 ∣ k := by
    have hkl : lam ∣ ((k * 3 ^ r : ℕ) : 𝓞 K5) := by
      have h' := dvd_trans (dvd_pow_self lam (by norm_num)) hX2
      have := dvd_sub (dvd_mul_left lam Y) h'
      push_cast; convert this using 1; rw [hX]; ring
    exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right r (by norm_num))
      (five_dvd_of_lam_dvd_nat hkl)
  -- 5 ∣ C
  have hC : 5 ∣ C := by
    have h2 : 2 * C = k * (k - 1) := by
      rw [hCdef]; exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)
    have : 5 ∣ 2 * C := by rw [h2]; exact Dvd.dvd.mul_right hk _
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this
  refine ⟨hk, ?_⟩
  have hk5 : lam ^ 2 ∣ (k : 𝓞 K5) * 3 ^ r := by
    have := lam_pow_dvd_of_five_dvd (m := ((k * 3 ^ r : ℕ) : ℤ))
      (by exact_mod_cast Dvd.dvd.mul_right hk _) (j := 2) (by norm_num)
    push_cast at this; exact this
  have hY1 : lam ∣ Y := by
    have h2 := dvd_add hX2 hk5
    have h3 : lam ^ (1 + 1) ∣ lam * Y := by
      rw [show lam * Y = X + (k : 𝓞 K5) * 3 ^ r by rw [hX]; ring]; simpa using h2
    simpa using lam_cancel h3
  have hCl : lam ∣ (C : 𝓞 K5) * 3 ^ r := by
    have := lam_pow_dvd_of_five_dvd (m := ((C * 3 ^ r : ℕ) : ℤ))
      (by exact_mod_cast Dvd.dvd.mul_right hC _) (j := 1) (by norm_num)
    push_cast at this; simpa using this
  have hrv : lam ∣ (r : 𝓞 K5) * 3 ^ (r - 1) * v5 := by
    have := dvd_sub hCl hY1; convert this using 1; rw [hY]; ring
  have hr4 : lam ∣ ((4 * (r * 3 ^ (r - 1)) : ℕ) : 𝓞 K5) := by
    have e : ((4 * (r * 3 ^ (r - 1)) : ℕ) : 𝓞 K5)
        = (r : 𝓞 K5) * 3 ^ (r - 1) * v5 - (r : 𝓞 K5) * 3 ^ (r - 1) * (v5 - 4) := by push_cast; ring
    rw [e]
    exact dvd_sub hrv (dvd_mul_of_dvd_right v5_congr _)
  have h5' : 5 ∣ r * 3 ^ (r - 1) :=
    Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) (five_dvd_of_lam_dvd_nat hr4)
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right _ (by norm_num)) h5'

lemma lam_pow_three_dvd_125 : lam ^ 3 ∣ (125 : 𝓞 K5) :=
  ⟨lam * u5 ^ 3 * 5 ^ 2 * 0 + lam ^ 9 * u5 ^ 3, by
    have := five_eq
    have e : (125 : 𝓞 K5) = 5 ^ 3 := by norm_num
    rw [e, ← this]; ring⟩

/-- **Kummer's lemma** for `l = 5`: a unit congruent to a rational integer modulo `λ³` is a
fifth power of a unit. -/
theorem kummer_lemma (ε : (𝓞 K5)ˣ) (n : ℤ) (h : lam ^ 3 ∣ (ε : 𝓞 K5) - n) :
    ∃ η : (𝓞 K5)ˣ, ε = η ^ 5 := by
  obtain ⟨k, m, s, hs, hε⟩ := unit_form ε
  set q := m / 5 with hq
  set r0 := (m % 5).toNat with hr0
  have hm : m = 5 * q + r0 := by
    have h2 : (0 : ℤ) ≤ m % 5 := Int.emod_nonneg m (by norm_num)
    rw [hr0, Int.toNat_of_nonneg h2, hq]; omega
  have hr05 : r0 < 5 := by
    have : m % 5 < 5 := Int.emod_lt_of_pos m (by norm_num)
    omega
  set β : (𝓞 K5)ˣ := Φ ^ q with hβ
  have hΦm : ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) = ((β : 𝓞 K5)) ^ 5 * φ ^ r0 := by
    rw [hm, zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val Φ r0]
    congr 1
    rw [hβ, ← Units.val_pow_eq_pow_val, show (5 : ℤ) * q = q * ((5 : ℕ) : ℤ) by push_cast; ring,
      zpow_mul, zpow_natCast]
  have hk : ζ ^ k = ζ ^ (k % 5) := by
    conv_lhs => rw [← Nat.mod_add_div k 5, pow_add, pow_mul, ζ_pow_five, one_pow, mul_one]
  obtain ⟨c, hc⟩ := exists_int_congr (β : 𝓞 K5)
  have hc5 := pow_five_congr hc
  -- c is prime to 5
  have hc_cop : IsCoprime (c ^ 5) 125 := by
    have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    have h5c : ¬ (5 : ℤ) ∣ c := by
      intro h5
      apply lam_not_dvd_one
      have hlc : lam ∣ (c : 𝓞 K5) := by simpa using lam_pow_dvd_of_five_dvd h5 (j := 1) (by norm_num)
      have hlb : lam ∣ (β : 𝓞 K5) := by have := dvd_add hc hlc; simpa using this
      exact dvd_trans hlb ⟨↑β⁻¹, by simp⟩
    have : IsCoprime c 5 := ((Prime.coprime_iff_not_dvd hp).mpr h5c).symm
    have e : (125 : ℤ) = 5 ^ 3 := by norm_num
    rw [e]; exact this.pow
  obtain ⟨a, b, hab⟩ := hc_cop
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  -- reduce to ζ^(k%5) φ^r0 ≡ integer mod λ³
  have hkey : lam ^ 3 ∣ ζ ^ (k % 5) * φ ^ r0 - ((s * a * n : ℤ) : 𝓞 K5) := by
    have e1 : (ε : 𝓞 K5) = s * ζ ^ (k % 5) * φ ^ r0 * (β : 𝓞 K5) ^ 5 := by
      rw [hε, hΦm, hk]; ring
    have hd : lam ^ 3 ∣ (s : 𝓞 K5) * ζ ^ (k % 5) * φ ^ r0 * ((β : 𝓞 K5) ^ 5 - (c : 𝓞 K5) ^ 5) :=
      dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow lam (by norm_num)) hc5) _
    have h' : lam ^ 3 ∣ (s : 𝓞 K5) * ζ ^ (k % 5) * φ ^ r0 * (β : 𝓞 K5) ^ 5 - n := by
      rw [← e1]; exact h
    have h3 : lam ^ 3 ∣ ((s * a : ℤ) : 𝓞 K5) *
        ((s : 𝓞 K5) * ζ ^ (k % 5) * φ ^ r0 * (c : 𝓞 K5) ^ 5 - n) := by
      apply dvd_mul_of_dvd_right
      have := dvd_sub h' hd
      convert this using 1; ring
    have h4 : lam ^ 3 ∣ ζ ^ (k % 5) * φ ^ r0 * ((b : 𝓞 K5) * 125) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_right lam_pow_three_dvd_125 _) _
    have h5 := dvd_add h3 h4
    convert h5 using 1
    have hab' : (a : 𝓞 K5) * (c : 𝓞 K5) ^ 5 + (b : 𝓞 K5) * 125 = 1 := by exact_mod_cast hab
    have hs2' : (s : 𝓞 K5) * s = 1 := by exact_mod_cast hs2
    push_cast
    linear_combination (-(ζ ^ (k % 5) * φ ^ r0)) * hab' + (-(a : 𝓞 K5) * ζ ^ (k % 5) * φ ^ r0 *
      (c : 𝓞 K5) ^ 5) * hs2'
  obtain ⟨h5k, h5r⟩ := kummer_core hkey
  have hk0 : k % 5 = 0 := by have := Nat.mod_lt k (by norm_num : 5 > 0); omega
  have hr00 : r0 = 0 := by omega
  rcases hs with rfl | rfl
  · refine ⟨β, ?_⟩
    apply Units.ext
    rw [hε, hΦm, hk, hk0, hr00]; simp
  · refine ⟨-β, ?_⟩
    apply Units.ext
    rw [hε, hΦm, hk, hk0, hr00]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg]
    push_cast; ring

end Kummer

section Two

/-- Product in coordinates. -/
lemma mul_coord (a b c e A B C E : ℤ) :
    ((a : 𝓞 K5) + b * ζ + c * ζ ^ 2 + e * ζ ^ 3) * ((A : 𝓞 K5) + B * ζ + C * ζ ^ 2 + E * ζ ^ 3)
    = ((A*a - B*e - C*c + C*e - E*b + E*c : ℤ) : 𝓞 K5)
      + ((A*b + B*a - B*e - C*c - E*b + E*e : ℤ) : 𝓞 K5) * ζ
      + ((A*c + B*b - B*e + C*a - C*c - E*b : ℤ) : 𝓞 K5) * ζ ^ 2
      + ((A*e + B*c - B*e + C*b - C*c + E*a - E*b : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  push_cast
  linear_combination ((B : 𝓞 K5)*e + C*c - C*e + E*b - E*c + E*e*ζ^2 + ζ*(C*e + E*c - E*e)) * cyc

lemma two_dvd_coord {a b c e : ℤ} (h : (2 : 𝓞 K5) ∣ (a : 𝓞 K5) + b * ζ + c * ζ ^ 2 + e * ζ ^ 3) :
    2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ e := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨a', b', c', e', rfl⟩ := exists_coord w
  have := coord_eq (a := a) (b := b) (c := c) (e := e) (a' := 2 * a') (b' := 2 * b') (c' := 2 * c')
    (e' := 2 * e') (by rw [hw]; push_cast; ring)
  obtain ⟨h1, h2, h3, h4⟩ := this
  exact ⟨⟨a', h1⟩, ⟨b', h2⟩, ⟨c', h3⟩, ⟨e', h4⟩⟩

lemma two_dvd_of_coord {a b c e : ℤ} (h : 2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c ∧ 2 ∣ e) :
    (2 : 𝓞 K5) ∣ (a : 𝓞 K5) + b * ζ + c * ζ ^ 2 + e * ζ ^ 3 := by
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨e', rfl⟩⟩ := h
  exact ⟨a' + b' * ζ + c' * ζ ^ 2 + e' * ζ ^ 3, by push_cast; ring⟩

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
set_option maxRecDepth 100000 in
/-- `F₂[x]/(x⁴+x³+x²+x+1)` has no zero divisors. -/
lemma F16_domain : ∀ a b c e A B C E : ZMod 2,
    A*a - B*e - C*c + C*e - E*b + E*c = 0 → A*b + B*a - B*e - C*c - E*b + E*e = 0 →
    A*c + B*b - B*e + C*a - C*c - E*b = 0 → A*e + B*c - B*e + C*b - C*c + E*a - E*b = 0 →
    (a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0) ∨ (A = 0 ∧ B = 0 ∧ C = 0 ∧ E = 0) := by decide

lemma even_iff_cast {n : ℤ} : 2 ∣ n ↔ (n : ZMod 2) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).symm

/-- `2` is prime in `ℤ[ζ₅]` (it is inert, with residue field `F₁₆`). -/
theorem two_prime : Prime (2 : 𝓞 K5) := by
  refine ⟨two_ne_zero, ?_, ?_⟩
  · intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨a, b, c, e, rfl⟩ := exists_coord v
    have := coord_eq (a := 2 * a) (b := 2 * b) (c := 2 * c) (e := 2 * e) (a' := 1) (b' := 0)
      (c' := 0) (e' := 0) (by push_cast; rw [← hv]; ring)
    omega
  · intro α β h
    obtain ⟨a, b, c, e, rfl⟩ := exists_coord α
    obtain ⟨A, B, C, E, rfl⟩ := exists_coord β
    rw [mul_coord] at h
    obtain ⟨h0, h1, h2, h3⟩ := two_dvd_coord h
    rw [even_iff_cast] at h0 h1 h2 h3
    push_cast at h0 h1 h2 h3
    rcases F16_domain _ _ _ _ _ _ _ _ h0 h1 h2 h3 with ⟨ha, hb, hc, he⟩ | ⟨ha, hb, hc, he⟩
    · left
      apply two_dvd_of_coord
      simp only [even_iff_cast]; exact ⟨ha, hb, hc, he⟩
    · right
      apply two_dvd_of_coord
      simp only [even_iff_cast]; exact ⟨ha, hb, hc, he⟩

/-- `F₁₆` as quadruples over `F₂` (basis `1, ζ, ζ², ζ³`). -/
abbrev F16 := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2

def mul16 (x y : F16) : F16 :=
  let (a, b, c, e) := x
  let (A, B, C, E) := y
  (A*a - B*e - C*c + C*e - E*b + E*c, A*b + B*a - B*e - C*c - E*b + E*e,
   A*c + B*b - B*e + C*a - C*c - E*b, A*e + B*c - B*e + C*b - C*c + E*a - E*b)

def pow5_16 (x : F16) : F16 := mul16 x (mul16 x (mul16 x (mul16 x x)))

/-- `α` reduces to `v` modulo 2. -/
def HasRed (α : 𝓞 K5) (v : F16) : Prop :=
  ∃ a b c e : ℤ, α = a + b * ζ + c * ζ ^ 2 + e * ζ ^ 3 ∧ v = ((a : ZMod 2), (b : ZMod 2), (c : ZMod 2), (e : ZMod 2))

lemma hasRed_exists (α : 𝓞 K5) : ∃ v, HasRed α v := by
  obtain ⟨a, b, c, e, h⟩ := exists_coord α
  exact ⟨_, a, b, c, e, h, rfl⟩

lemma HasRed.mul {α β : 𝓞 K5} {v w : F16} (hα : HasRed α v) (hβ : HasRed β w) :
    HasRed (α * β) (mul16 v w) := by
  obtain ⟨a, b, c, e, rfl, rfl⟩ := hα
  obtain ⟨A, B, C, E, rfl, rfl⟩ := hβ
  refine ⟨_, _, _, _, mul_coord a b c e A B C E, ?_⟩
  simp only [mul16]; push_cast; rfl

lemma HasRed.add {α β : 𝓞 K5} {v w : F16} (hα : HasRed α v) (hβ : HasRed β w) :
    HasRed (α + β) (v + w) := by
  obtain ⟨a, b, c, e, rfl, rfl⟩ := hα
  obtain ⟨A, B, C, E, rfl, rfl⟩ := hβ
  refine ⟨a + A, b + B, c + C, e + E, by push_cast; ring, ?_⟩
  push_cast; rfl

lemma hasRed_ζ : HasRed ζ (0, 1, 0, 0) := ⟨0, 1, 0, 0, by push_cast; ring, by rfl⟩

lemma HasRed.pow5 {α : 𝓞 K5} {v : F16} (h : HasRed α v) : HasRed (α ^ 5) (pow5_16 v) := by
  have := h.mul (h.mul (h.mul (h.mul h)))
  simpa [pow5_16, pow_succ, mul_comm, mul_assoc, mul_left_comm] using this

lemma HasRed.two_dvd {α : 𝓞 K5} {v : F16} (h : HasRed α v) : (2 : 𝓞 K5) ∣ α ↔ v = 0 := by
  obtain ⟨a, b, c, e, rfl, rfl⟩ := h
  constructor
  · intro h2
    obtain ⟨h0, h1, h2', h3⟩ := two_dvd_coord h2
    rw [even_iff_cast] at h0 h1 h2' h3
    simp [h0, h1, h2', h3]
  · intro h0
    simp only [Prod.mk_eq_zero] at h0
    apply two_dvd_of_coord
    simp only [even_iff_cast]; exact ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2⟩

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
set_option maxRecDepth 100000 in
lemma F16_zeta_not_fifth : ∀ x y : F16, mul16 (0, 1, 0, 0) (pow5_16 y) + pow5_16 x = 0 → y = 0 := by
  decide

/-- `ζ` is not a fifth power modulo `2`: if `2 ∣ ζ y⁵ + x⁵` then `2 ∣ y`. -/
theorem zeta_not_fifth_mod_two {x y : 𝓞 K5} (h : (2 : 𝓞 K5) ∣ ζ * y ^ 5 + x ^ 5) :
    (2 : 𝓞 K5) ∣ y := by
  obtain ⟨v, hv⟩ := hasRed_exists x
  obtain ⟨w, hw⟩ := hasRed_exists y
  have hred := (hasRed_ζ.mul hw.pow5).add hv.pow5
  rw [hred.two_dvd] at h
  exact hw.two_dvd.mpr (F16_zeta_not_fifth v w h)

end Two

section CaseB

open NumberField.IsCMField

lemma prod_five (x y : 𝓞 K5) :
    (x + y) * (x + ζ * y) * (x + ζ ^ 2 * y) * (x + ζ ^ 3 * y) * (x + ζ ^ 4 * y) = x ^ 5 + y ^ 5 := by
  linear_combination (x ^ 4 * y - y ^ 5 + ζ ^ 6 * (x * y ^ 4 + y ^ 5) + ζ ^ 5 * (x ^ 2 * y ^ 3 - y ^ 5)
    + ζ ^ 3 * (x ^ 3 * y ^ 2 + x ^ 2 * y ^ 3) + ζ * (x ^ 3 * y ^ 2 + y ^ 5)) * cyc

lemma prod_one_sub : (1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4) = 5 := by
  linear_combination (ζ ^ 6 - 2 * ζ ^ 5 + ζ ^ 3 + 3 * ζ - 4) * cyc

lemma hasRed_ζ4 : HasRed (ζ ^ 4) (1, 1, 1, 1) :=
  ⟨-1, -1, -1, -1, by push_cast; linear_combination cyc, by decide⟩

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
set_option maxRecDepth 100000 in
lemma F16_zeta4_not_fifth : ∀ x y : F16, mul16 (1, 1, 1, 1) (pow5_16 y) + pow5_16 x = 0 → y = 0 := by
  decide

theorem zeta4_not_fifth_mod_two {x y : 𝓞 K5} (h : (2 : 𝓞 K5) ∣ ζ ^ 4 * y ^ 5 + x ^ 5) :
    (2 : 𝓞 K5) ∣ y := by
  obtain ⟨v, hv⟩ := hasRed_exists x
  obtain ⟨w, hw⟩ := hasRed_exists y
  have hred := (hasRed_ζ4.mul hw.pow5).add hv.pow5
  rw [hred.two_dvd] at h
  exact hw.two_dvd.mpr (F16_zeta4_not_fifth v w h)

/-- The differences `ζ^i - ζ` (`i = 0, 2, 3, 4`) divide `5`. -/
lemma diff_dvd_five (i : ℕ) (hi : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) : (ζ ^ i - ζ) ∣ (5 : 𝓞 K5) := by
  rw [← prod_one_sub]
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨(1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4), by ring⟩
  · exact ⟨-(ζ ^ 4 * (1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4)), by
      linear_combination (-((1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4))) * ζ_pow_five⟩
  · exact ⟨-(ζ ^ 4 * (1 - ζ) * (1 - ζ ^ 3) * (1 - ζ ^ 4)), by
      linear_combination (-((1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4))) * ζ_pow_five⟩
  · exact ⟨-(ζ ^ 4 * (1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 4)), by
      linear_combination (-((1 - ζ) * (1 - ζ ^ 2) * (1 - ζ ^ 3) * (1 - ζ ^ 4))) * ζ_pow_five⟩

/-- Coprimality of `x + ζ y` with the other factors, when `5 ∣ y` and `x, y` coprime. -/
lemma coprime_F1 {x y : ℤ} (hxy : IsCoprime x y) (hx5 : IsCoprime x 5) (hy5 : (5 : ℤ) ∣ y)
    (i : ℕ) (hi : i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4) :
    IsCoprime ((x : 𝓞 K5) + ζ * y) ((x : 𝓞 K5) + ζ ^ i * y) := by
  obtain ⟨y', rfl⟩ := hy5
  obtain ⟨a, b, hab⟩ := hx5
  have h5 : IsCoprime ((x : 𝓞 K5) + ζ * ((5 * y' : ℤ) : 𝓞 K5)) 5 := by
    refine ⟨a, b - a * ζ * y', ?_⟩
    have : ((a * x + b * 5 : ℤ) : 𝓞 K5) = 1 := by rw [hab]; simp
    push_cast at this ⊢; linear_combination this
  have hd := h5.of_isCoprime_of_dvd_right (diff_dvd_five i hi)
  obtain ⟨p, q, hpq⟩ := hxy
  obtain ⟨r, t, hrt⟩ := hd
  set F1 := (x : 𝓞 K5) + ζ * ((5 * y' : ℤ) : 𝓞 K5)
  set Fi := (x : 𝓞 K5) + ζ ^ i * ((5 * y' : ℤ) : 𝓞 K5)
  have hpq' : (p : 𝓞 K5) * x + q * ((5 * y' : ℤ) : 𝓞 K5) = 1 := by exact_mod_cast hpq
  refine ⟨r + t * p * ζ ^ i - t * q, t * (q - p * ζ), ?_⟩
  rw [← hrt]
  have e : ζ ^ i - ζ = (p : 𝓞 K5) * (ζ ^ i * F1 - ζ * Fi) + q * (Fi - F1) := by
    simp only [F1, Fi]; linear_combination (-(ζ ^ i - ζ)) * hpq'
  rw [e]; ring

/-- **Case b** of Dénes for `l = 5`: no solution of `x⁵ + y⁵ = 2^j z⁵` (`j ≥ 1`) with `x, y`
coprime and `5 ∣ y`. -/
theorem case_b {x y z : ℤ} {j : ℕ} (hj : 1 ≤ j) (h : x ^ 5 + y ^ 5 = 2 ^ j * z ^ 5)
    (hxy : IsCoprime x y) (hy5 : (5 : ℤ) ∣ y) : False := by
  -- parity: x and y are odd
  have hev : Even (x ^ 5 + y ^ 5) := by
    rw [h]; exact ⟨2 ^ (j - 1) * z ^ 5, by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring⟩
  have hxodd : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := by
        rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at hev
        exact hev.mp hx
      have := hxy.isUnit_of_dvd' hx.two_dvd hy.two_dvd
      rcases Int.isUnit_iff.mp this with h | h <;> norm_num at h
    · exact hx
  have hyodd : Odd y := by
    rw [Int.even_add, Int.even_pow' (by norm_num), Int.even_pow' (by norm_num)] at hev
    rcases Int.even_or_odd y with hy | hy
    · exact absurd (hev.mpr hy) (Int.not_even_iff_odd.mpr hxodd)
    · exact hy
  have hx5 : IsCoprime x 5 := by
    have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    refine ((Prime.coprime_iff_not_dvd hp).mpr ?_).symm
    intro h5x
    exact hp.not_isUnit (hxy.isUnit_of_dvd' h5x hy5)
  set F1 : 𝓞 K5 := (x : 𝓞 K5) + ζ * y with hF1
  set R : 𝓞 K5 := ((x : 𝓞 K5) + y) * ((x : 𝓞 K5) + ζ ^ 2 * y) * ((x : 𝓞 K5) + ζ ^ 3 * y)
    * ((x : 𝓞 K5) + ζ ^ 4 * y) with hR
  have hFR : F1 * R = 2 ^ j * (z : 𝓞 K5) ^ 5 := by
    have := prod_five (x : 𝓞 K5) (y : 𝓞 K5)
    have h' : ((x ^ 5 + y ^ 5 : ℤ) : 𝓞 K5) = ((2 ^ j * z ^ 5 : ℤ) : 𝓞 K5) := by rw [h]
    push_cast at h'
    rw [hF1, hR, ← h', ← this]; ring
  have hcopR : IsCoprime F1 R := by
    have c0 := coprime_F1 hxy hx5 hy5 0 (by norm_num)
    have c2 := coprime_F1 hxy hx5 hy5 2 (by norm_num)
    have c3 := coprime_F1 hxy hx5 hy5 3 (by norm_num)
    have c4 := coprime_F1 hxy hx5 hy5 4 (by norm_num)
    simp only [pow_zero, one_mul] at c0
    exact ((c0.mul_right c2).mul_right c3).mul_right c4
  -- 2 does not divide F1
  have h2F1 : ¬ (2 : 𝓞 K5) ∣ F1 := by
    intro h2
    have : (2 : 𝓞 K5) ∣ (x : 𝓞 K5) + y * ζ + (0 : ℤ) * ζ ^ 2 + (0 : ℤ) * ζ ^ 3 := by
      convert h2 using 1; rw [hF1]; push_cast; ring
    obtain ⟨h2x, -⟩ := two_dvd_coord this
    exact (Int.not_even_iff_odd.mpr hxodd) (even_iff_two_dvd.mpr h2x)
  have hcop2 : IsCoprime ((2 : 𝓞 K5) ^ j) F1 :=
    ((Prime.coprime_iff_not_dvd two_prime).mpr h2F1).pow_left
  have h2R : (2 : 𝓞 K5) ^ j ∣ R := hcop2.dvd_of_dvd_mul_left ⟨(z : 𝓞 K5) ^ 5, hFR⟩
  obtain ⟨R', hR'⟩ := h2R
  have hFR' : F1 * R' = (z : 𝓞 K5) ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero j two_ne_zero)
    rw [← hFR, hR']; ring
  have hcopR' : IsCoprime F1 R' := hcopR.of_isCoprime_of_dvd_right ⟨_, by rw [hR', mul_comm]⟩
  obtain ⟨α, u, hαu⟩ := exists_associated_pow_of_mul_eq_pow' hcopR' hFR'
  -- F1 ≡ x (mod λ⁴)
  obtain ⟨y', rfl⟩ := hy5
  have hF1x : lam ^ 4 ∣ F1 - x := by
    rw [hF1]; push_cast
    exact ⟨u5 * ζ * y', by linear_combination (-(ζ * y')) * five_eq⟩
  -- λ does not divide α
  have hlα : ¬ lam ∣ α := by
    intro hl
    have h1 : lam ∣ F1 := by rw [← hαu]; exact dvd_mul_of_dvd_left (dvd_pow hl (by norm_num)) _
    have h2 : lam ∣ (x : 𝓞 K5) := by
      have := dvd_sub h1 (dvd_trans (dvd_pow_self lam (by norm_num)) hF1x); simpa using this
    have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    exact hp.not_isUnit (hx5.isUnit_of_dvd' (lam_dvd_int h2) (dvd_refl 5))
  obtain ⟨c0, hc0⟩ := exists_int_congr α
  have hc05 := pow_five_congr hc0
  have hc0_cop : IsCoprime (c0 ^ 5) 125 := by
    have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    have h5c : ¬ (5 : ℤ) ∣ c0 := by
      intro h5
      apply hlα
      have hlc : lam ∣ (c0 : 𝓞 K5) := by simpa using lam_pow_dvd_of_five_dvd h5 (j := 1) (by norm_num)
      have := dvd_add hc0 hlc; simpa using this
    have : IsCoprime c0 5 := ((Prime.coprime_iff_not_dvd hp).mpr h5c).symm
    have e : (125 : ℤ) = 5 ^ 3 := by norm_num
    rw [e]; exact this.pow
  obtain ⟨a, b, hab⟩ := hc0_cop
  -- the unit u is congruent to an integer mod λ³
  have hu : lam ^ 3 ∣ ((u : 𝓞 K5)) - ((a * x : ℤ) : 𝓞 K5) := by
    have e1 : lam ^ 3 ∣ α ^ 5 * u - x := by
      rw [hαu]; exact dvd_trans (pow_dvd_pow lam (by norm_num)) hF1x
    have e2 : lam ^ 3 ∣ (α ^ 5 - (c0 : 𝓞 K5) ^ 5) * u :=
      dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow lam (by norm_num)) hc05) _
    have e3 : lam ^ 3 ∣ (a : 𝓞 K5) * ((c0 : 𝓞 K5) ^ 5 * u - x) := by
      apply dvd_mul_of_dvd_right; have := dvd_sub e1 e2; convert this using 1; ring
    have e4 : lam ^ 3 ∣ (b : 𝓞 K5) * 125 * u := dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right lam_pow_three_dvd_125 _) _
    have hab' : (a : 𝓞 K5) * (c0 : 𝓞 K5) ^ 5 + (b : 𝓞 K5) * 125 = 1 := by exact_mod_cast hab
    have := dvd_add e3 e4
    convert this using 1; push_cast; linear_combination (-(u : 𝓞 K5)) * hab'
  obtain ⟨η, hη⟩ := kummer_lemma u (a * x) hu
  set β : 𝓞 K5 := α * η with hβ
  have hFβ : F1 = β ^ 5 := by rw [← hαu, hη, hβ]; push_cast; ring
  -- conjugate factor
  have hσF : σ F1 = (x : 𝓞 K5) + ζ ^ 4 * ((5 * y' : ℤ) : 𝓞 K5) := by
    rw [hF1]; simp only [map_add, map_mul, map_intCast, σ_ζ]
  have hsum : ζ ^ 4 * F1 + σ F1 = (1 + ζ ^ 4) * ((x : 𝓞 K5) + ((5 * y' : ℤ) : 𝓞 K5)) := by
    rw [hσF, hF1]; linear_combination ((5 * y' : ℤ) : 𝓞 K5) * ζ_pow_five
  have h2sum : (2 : 𝓞 K5) ∣ ζ ^ 4 * β ^ 5 + (σ β) ^ 5 := by
    rw [← map_pow, ← hFβ, hsum]
    apply dvd_mul_of_dvd_right
    have : Even (x + 5 * y') := hxodd.add_odd hyodd
    obtain ⟨w, hw⟩ := this
    have hw' := congrArg (fun t : ℤ => (t : 𝓞 K5)) hw
    push_cast at hw'
    exact ⟨(w : 𝓞 K5), by push_cast; linear_combination hw'⟩
  have h2β := zeta4_not_fifth_mod_two h2sum
  exact h2F1 (by rw [hFβ]; exact dvd_pow h2β (by norm_num))

end CaseB

section CasePrereq

instance oma_fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma lam_prime : Prime lam := by
  have h := hζ5.zeta_sub_one_prime'
  have e : lam = -(hζ5.toInteger - 1) := by simp [lam, ζ]
  rw [e]; exact h.neg

lemma isUnit_of_mul {a b : 𝓞 K5} (h : a * b = 1) : IsUnit a :=
  ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩

/-- `1 - ζ^k = λ · (unit)` for `k = 1, 2, 3, 4`. -/
lemma one_sub_pow_eq (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) :
    ∃ w : 𝓞 K5, IsUnit w ∧ 1 - ζ ^ k = lam * w := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨1, isUnit_one, by ring⟩
  · refine ⟨1 + ζ, isUnit_of_mul (b := -ζ ^ 3 - ζ) ?_, by ring⟩
    linear_combination (-1 : 𝓞 K5) * cyc
  · refine ⟨1 + ζ + ζ ^ 2, isUnit_of_mul (b := ζ ^ 3 + 1) ?_, by ring⟩
    linear_combination ζ * cyc
  · refine ⟨1 + ζ + ζ ^ 2 + ζ ^ 3, isUnit_of_mul (b := -ζ) ?_, by ring⟩
    linear_combination (-1 : 𝓞 K5) * cyc

end CasePrereq

end OMA672Z5
