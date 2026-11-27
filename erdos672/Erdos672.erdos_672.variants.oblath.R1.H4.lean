import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1
import Mathlib

-- Step Erdos672.erdos_672.variants.oblath.R1.H4: hypothesis H4 of reduction Erdos672.erdos_672.variants.oblath.R1
-- Credit: @aqron7
-- H4 := Erdos672.Erdos672With 3 5

/-! The product of three consecutive terms of a primitive arithmetic progression is never a fifth
power. Reduction to `x^5 + y^5 = 2 z^5` and `x^5 + y^5 = 8 z^5`, which are settled here by a full
formalisation of Denes (1952) for `l = 5`: Kummer theory in `Z[zeta_5]` (Kummer's lemma, unit
group), case `5 | y` (mod 2 obstruction), case `5 | z` (Maillet descent), and case `5 ∤ xyz` by a
descent over the real subfield whose key input is Eisenstein reciprocity for the prime `2`
(proved via Jacobi sums). -/

-- ===== Zeta5.lean =====

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

lemma u5_isUnit : IsUnit u5 := by
  obtain ⟨w2, hw2, e2⟩ := one_sub_pow_eq 2 (by norm_num)
  obtain ⟨w3, hw3, e3⟩ := one_sub_pow_eq 3 (by norm_num)
  obtain ⟨w4, hw4, e4⟩ := one_sub_pow_eq 4 (by norm_num)
  have h2 : w2 = 1 + ζ := mul_left_cancel₀ lam_ne_zero (by rw [← e2]; ring)
  have h3 : w3 = 1 + ζ + ζ ^ 2 := mul_left_cancel₀ lam_ne_zero (by rw [← e3]; ring)
  have h4 : w4 = 1 + ζ + ζ ^ 2 + ζ ^ 3 := mul_left_cancel₀ lam_ne_zero (by rw [← e4]; ring)
  rw [h2] at hw2; rw [h3] at hw3; rw [h4] at hw4
  exact (hw2.mul hw3).mul hw4

lemma zmod5_pow_four : ∀ a : ZMod 5, a ≠ 0 → a ^ 4 = 1 := by decide

/-- Normalisation: every `x` prime to `λ` is, after multiplying by a power of `ζ`,
congruent to a rational integer modulo `λ²`. -/
lemma normalize {x : 𝓞 K5} (hx : ¬ lam ∣ x) : ∃ k : ℕ, ∃ a : ℤ, lam ^ 2 ∣ ζ ^ k * x - a := by
  obtain ⟨a0, ha0⟩ := exists_int_congr x
  obtain ⟨t, ht⟩ := ha0
  obtain ⟨b, hb⟩ := exists_int_congr t
  have ha05 : ¬ (5 : ℤ) ∣ a0 := by
    intro h5; apply hx
    have := dvd_add (⟨t, ht⟩ : lam ∣ x - a0) (by simpa using lam_pow_dvd_of_five_dvd h5 (j := 1) (by norm_num))
    simpa using this
  set k : ℕ := ((b * a0 ^ 3) % 5).toNat with hk
  have hkmod : (5 : ℤ) ∣ b - k * a0 := by
    have hk' : ((k : ℤ) : ZMod 5) = ((b * a0 ^ 3 : ℤ) : ZMod 5) := by
      rw [hk, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact ZMod.intCast_mod _ _
    have ha : ((a0 : ℤ) : ZMod 5) ≠ 0 := by
      intro h0; exact ha05 (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd a0 5).mp h0)
    have h0 : ((b - k * a0 : ℤ) : ZMod 5) = 0 := by
      push_cast at hk' ⊢
      rw [hk', mul_assoc, ← pow_succ, zmod5_pow_four _ ha]; ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h0
  obtain ⟨P, hP⟩ := one_sub_pow k
  refine ⟨k, a0, ?_⟩
  obtain ⟨b', hb'⟩ := hkmod
  obtain ⟨t', ht'⟩ := hb
  have hlb : lam ∣ ((b - k * a0 : ℤ) : 𝓞 K5) :=
    by simpa using lam_pow_dvd_of_five_dvd (⟨b', hb'⟩ : (5 : ℤ) ∣ b - k * a0) (j := 1) (by norm_num)
  obtain ⟨m, hm⟩ := hlb
  have hx' : x = a0 + lam * (b + lam * t') := by linear_combination ht + lam * ht'
  set C : 𝓞 K5 := ((k * (k - 1) / 2 : ℕ) : 𝓞 K5)
  refine ⟨m + (t' - k * b - k * lam * t' + C * a0 + C * b * lam + C * lam ^ 2 * t' + lam * P * a0
    + lam ^ 2 * P * b + lam ^ 3 * P * t'), ?_⟩
  rw [ζ_eq, hP, hx']
  push_cast at hm
  linear_combination lam * hm

end CasePrereq

section CaseC

/-- `ζ^s - ζ^r = λ · (unit)` for `r < s < 5`. -/
lemma diff_eq {r s : ℕ} (hrs : r < s) (hs : s < 5) : ∃ w : 𝓞 K5, IsUnit w ∧ ζ ^ s - ζ ^ r = lam * w := by
  obtain ⟨w, hw, he⟩ := one_sub_pow_eq (s - r) (by omega)
  refine ⟨-(ζ ^ r * w), (((hζ5.toInteger_isPrimitiveRoot.isUnit (by norm_num)).pow r).mul hw).neg, ?_⟩
  have : ζ ^ s = ζ ^ r * ζ ^ (s - r) := by rw [← pow_add]; congr 1; omega
  rw [this]; linear_combination (-(ζ ^ r)) * he

/-- If two factors `u + ζ^r v`, `u + ζ^s v` are `λ X`, `λ Y`, then `X, Y` are coprime. -/
lemma coprime_quot {u v X Y w : 𝓞 K5} {r s : ℕ} (hcop : IsCoprime u v)
    (hX : u + ζ ^ r * v = lam * X) (hY : u + ζ ^ s * v = lam * Y)
    (hw : ζ ^ s - ζ ^ r = lam * w) (hwu : IsUnit w) : IsCoprime X Y := by
  obtain ⟨p, q, hpq⟩ := hcop
  have key : w = p * (ζ ^ s * X - ζ ^ r * Y) + q * (Y - X) := by
    apply mul_left_cancel₀ lam_ne_zero
    rw [← hw]
    linear_combination (-(ζ ^ s - ζ ^ r)) * hpq + (p * ζ ^ s - q) * hX + (q - p * ζ ^ r) * hY
  obtain ⟨wu, rfl⟩ := hwu
  refine ⟨↑wu⁻¹ * (p * ζ ^ s - q), ↑wu⁻¹ * (q - p * ζ ^ r), ?_⟩
  have : (↑wu⁻¹ : 𝓞 K5) * wu = 1 := by simp
  rw [← this, key]; ring

lemma zmod5_fermat : ∀ a : ZMod 5, a ^ 5 = a := by decide

lemma five_dvd_add_of_pow {a b : ℤ} (h : (5 : ℤ) ∣ a ^ 5 + b ^ 5) : (5 : ℤ) ∣ a + b := by
  have h0 : ((a ^ 5 + b ^ 5 : ℤ) : ZMod 5) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  have h1 : ((a + b : ℤ) : ZMod 5) = 0 := by
    push_cast at h0 ⊢; rwa [zmod5_fermat, zmod5_fermat] at h0
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h1

lemma pow_congr {m x y : 𝓞 K5} (n : ℕ) (h : m ∣ x - y) : m ∣ x ^ n - y ^ n :=
  dvd_trans h (sub_dvd_pow_sub_pow x y n)

lemma lam_not_dvd_two : ¬ lam ∣ (2 : 𝓞 K5) := by
  intro h
  have := lam_dvd_int (m := 2) (by exact_mod_cast h)
  norm_num at this

/-- Extract a fifth power from a factor coprime to the rest and to `2`. -/
lemma fifth_of_coprime {γ R w : 𝓞 K5} {E : (𝓞 K5)ˣ} {j : ℕ} (hcop : IsCoprime γ R)
    (h2 : ¬ (2 : 𝓞 K5) ∣ γ) (h : γ * R = E * 2 ^ j * w ^ 5) :
    ∃ t : 𝓞 K5, ∃ e : (𝓞 K5)ˣ, γ = e * t ^ 5 := by
  have hcop2 : IsCoprime ((2 : 𝓞 K5) ^ j) γ :=
    ((Prime.coprime_iff_not_dvd two_prime).mpr h2).pow_left
  have hE : (↑E⁻¹ : 𝓞 K5) * ↑E = 1 := by simp
  have hγE : γ * (↑E⁻¹ * R) = 2 ^ j * w ^ 5 := by
    rw [show γ * (↑E⁻¹ * R) = ↑E⁻¹ * (γ * R) by ring, h]
    linear_combination (2 ^ j * w ^ 5 : 𝓞 K5) * hE
  have h2R : (2 : 𝓞 K5) ^ j ∣ ↑E⁻¹ * R := hcop2.dvd_of_dvd_mul_left ⟨w ^ 5, hγE⟩
  obtain ⟨R', hR'⟩ := h2R
  have hγR' : γ * R' = w ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero j two_ne_zero)
    calc (2 : 𝓞 K5) ^ j * (γ * R') = γ * (2 ^ j * R') := by ring
      _ = γ * (↑E⁻¹ * R) := by rw [hR']
      _ = ↑E⁻¹ * (γ * R) := by ring
      _ = 2 ^ j * w ^ 5 := by rw [h]; linear_combination (2 ^ j * w ^ 5 : 𝓞 K5) * hE
  have hcopR' : IsCoprime γ R' := by
    have : IsCoprime γ (↑E⁻¹ * R) := (isCoprime_mul_unit_left_right E⁻¹.isUnit γ R).mpr hcop
    exact this.of_isCoprime_of_dvd_right ⟨2 ^ j, by rw [hR']; ring⟩
  obtain ⟨t, e, he⟩ := exists_associated_pow_of_mul_eq_pow' hcopR' hγR'
  exact ⟨t, e, by rw [← he, mul_comm]⟩

lemma not_lam_dvd_unit (e : (𝓞 K5)ˣ) : ¬ lam ∣ (e : 𝓞 K5) := by
  intro h; apply lam_not_dvd_one
  exact dvd_trans h ⟨↑e⁻¹, by simp⟩

lemma not_lam_dvd_mul {a b : 𝓞 K5} (ha : ¬ lam ∣ a) (hb : ¬ lam ∣ b) : ¬ lam ∣ a * b := by
  intro h; rcases lam_prime.dvd_or_dvd h with h | h <;> contradiction

lemma not_lam_dvd_pow {a : 𝓞 K5} (ha : ¬ lam ∣ a) (n : ℕ) : ¬ lam ∣ a ^ n := by
  intro h; exact ha (lam_prime.dvd_of_dvd_pow h)

lemma not_lam_dvd_two_pow (n : ℕ) : ¬ lam ∣ (2 : 𝓞 K5) ^ n := not_lam_dvd_pow lam_not_dvd_two n

/-- The factor `u + ζ^i v` is `λ γ` with `λ ∤ γ`, when `λ² ∣ u + v` and `λ ∤ v`. -/
lemma factor_i {u v : 𝓞 K5} (hv : ¬ lam ∣ v) (h2 : lam ^ 2 ∣ u + v) (i : ℕ)
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) : ∃ γ : 𝓞 K5, u + ζ ^ i * v = lam * γ ∧ ¬ lam ∣ γ := by
  obtain ⟨w, hw, he⟩ := one_sub_pow_eq i hi
  obtain ⟨m, hm⟩ := h2
  refine ⟨lam * m - w * v, by linear_combination hm - v * he, ?_⟩
  intro hl
  have : lam ∣ w * v := by have := dvd_sub (dvd_mul_right lam m) hl; simpa using this
  rcases lam_prime.dvd_or_dvd this with h | h
  · obtain ⟨wu, rfl⟩ := hw; exact not_lam_dvd_unit wu h
  · exact hv h

/-- Uniform finish of the descent once a good pair `r < s` is chosen. -/
lemma maillet_finish {μ : ℕ} (hμ : 1 ≤ μ)
    (IH : ∀ (j : ℕ) (u v w : 𝓞 K5) (E : (𝓞 K5)ˣ), ¬ lam ∣ u → ¬ lam ∣ v → ¬ lam ∣ w →
      IsCoprime u v → u ^ 5 + v ^ 5 = E * lam ^ (5 * (μ - 1) + 5) * 2 ^ j * w ^ 5 → False)
    {u v γ0 γr γs : 𝓞 K5} {r s : ℕ} (hrs : r < s) (hs5 : s < 5) (hr1 : 1 ≤ r)
    (h0 : u + v = lam ^ (5 * μ + 1) * γ0) (hr : u + ζ ^ r * v = lam * γr)
    (hsv : u + ζ ^ s * v = lam * γs)
    (hcrs : IsCoprime γr γs) (hlr : ¬ lam ∣ γr) (hls : ¬ lam ∣ γs) (hl0 : ¬ lam ∣ γ0)
    {er es : (𝓞 K5)ˣ} {tr ts : 𝓞 K5} (her : γr = er * tr ^ 5) (hes : γs = es * ts ^ 5)
    {j0 : ℕ} {e0 : (𝓞 K5)ˣ} {w0 : 𝓞 K5} (he0 : γ0 = 2 ^ j0 * (e0 * w0 ^ 5)) : False := by
  obtain ⟨wr, hwr, her'⟩ := one_sub_pow_eq r (by omega)
  obtain ⟨ws, hws, hes'⟩ := one_sub_pow_eq s (by omega)
  obtain ⟨wrs, hwrs, herss⟩ := diff_eq hrs hs5
  -- elimination: -ws γr + wr γs = wrs λ^(5μ) γ0
  have hel : -(ws * γr) + wr * γs = wrs * lam ^ (5 * μ) * γ0 := by
    have hid : (ζ ^ s - 1) * (u + ζ ^ r * v) - (ζ ^ r - 1) * (u + ζ ^ s * v) = (ζ ^ s - ζ ^ r) * (u + v) := by
      ring
    rw [hr, hsv, h0, herss, show ζ ^ s - 1 = -(1 - ζ ^ s) by ring, show ζ ^ r - 1 = -(1 - ζ ^ r) by ring,
      hes', her'] at hid
    apply mul_left_cancel₀ (pow_ne_zero 2 lam_ne_zero)
    linear_combination hid
  -- units
  obtain ⟨Ws, rfl⟩ := hws
  obtain ⟨Wr, rfl⟩ := hwr
  obtain ⟨Wrs, rfl⟩ := hwrs
  set A : (𝓞 K5)ˣ := -(Ws * er) with hA
  set ε : (𝓞 K5)ˣ := A⁻¹ * (Wr * es) with hε
  set E2 : (𝓞 K5)ˣ := A⁻¹ * (Wrs * e0) with hE2
  have hAA : (A : 𝓞 K5) * ↑A⁻¹ = 1 := by simp
  have hAv : (A : 𝓞 K5) = -((Ws : 𝓞 K5) * er) := by simp [hA]
  have hεv : (ε : 𝓞 K5) = ↑A⁻¹ * ((Wr : 𝓞 K5) * es) := by simp [hε]
  have hE2v : (E2 : 𝓞 K5) = ↑A⁻¹ * ((Wrs : 𝓞 K5) * e0) := by simp [hE2]
  have hnew : tr ^ 5 + (ε : 𝓞 K5) * ts ^ 5 = E2 * lam ^ (5 * μ) * 2 ^ j0 * w0 ^ 5 := by
    rw [her, hes, he0] at hel
    have key : (A : 𝓞 K5) * (tr ^ 5 + (ε : 𝓞 K5) * ts ^ 5)
        = A * (E2 * lam ^ (5 * μ) * 2 ^ j0 * w0 ^ 5) := by
      rw [hεv, hE2v]
      have e1 : (A : 𝓞 K5) * (tr ^ 5 + ↑A⁻¹ * ((Wr : 𝓞 K5) * es) * ts ^ 5)
          = A * tr ^ 5 + (A * ↑A⁻¹) * ((Wr : 𝓞 K5) * es * ts ^ 5) := by ring
      have e2 : (A : 𝓞 K5) * (↑A⁻¹ * ((Wrs : 𝓞 K5) * e0) * lam ^ (5 * μ) * 2 ^ j0 * w0 ^ 5)
          = (A * ↑A⁻¹) * ((Wrs : 𝓞 K5) * e0 * lam ^ (5 * μ) * 2 ^ j0 * w0 ^ 5) := by ring
      rw [e1, e2, hAA, hAv]
      linear_combination hel
    exact mul_left_cancel₀ A.ne_zero key
  -- Kummer: ε is a fifth power
  have hltr : ¬ lam ∣ tr := fun h => hlr (by rw [her]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
  have hlts : ¬ lam ∣ ts := fun h => hls (by rw [hes]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _)
  have hlw0 : ¬ lam ∣ w0 := by
    intro h; apply hl0; rw [he0]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _) _
  obtain ⟨cr, hcr⟩ := exists_int_congr tr
  obtain ⟨cs, hcs⟩ := exists_int_congr ts
  have hcr5 := pow_five_congr hcr
  have hcs5 := pow_five_congr hcs
  have h5 : lam ^ 5 ∣ tr ^ 5 + (ε : 𝓞 K5) * ts ^ 5 := by
    rw [hnew]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow lam (by omega)) _) _) _
  have hcop_cs : IsCoprime (cs ^ 5) 125 := by
    have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
    have h5c : ¬ (5 : ℤ) ∣ cs := by
      intro h5; apply hlts
      have hlc : lam ∣ (cs : 𝓞 K5) := by simpa using lam_pow_dvd_of_five_dvd h5 (j := 1) (by norm_num)
      have := dvd_add hcs hlc; simpa using this
    have : IsCoprime cs 5 := ((Prime.coprime_iff_not_dvd hp).mpr h5c).symm
    rw [show (125 : ℤ) = 5 ^ 3 by norm_num]; exact this.pow
  obtain ⟨a, b, hab⟩ := hcop_cs
  have hεc : lam ^ 3 ∣ (ε : 𝓞 K5) - ((-(a * cr ^ 5)) : ℤ) := by
    have e1 : lam ^ 3 ∣ tr ^ 5 + (ε : 𝓞 K5) * ts ^ 5 := dvd_trans (pow_dvd_pow lam (by norm_num)) h5
    have e2 : lam ^ 3 ∣ (tr ^ 5 - (cr : 𝓞 K5) ^ 5) + (ε : 𝓞 K5) * (ts ^ 5 - (cs : 𝓞 K5) ^ 5) :=
      dvd_add (dvd_trans (pow_dvd_pow lam (by norm_num)) hcr5)
        (dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow lam (by norm_num)) hcs5) _)
    have e3 : lam ^ 3 ∣ (a : 𝓞 K5) * ((cr : 𝓞 K5) ^ 5 + (ε : 𝓞 K5) * (cs : 𝓞 K5) ^ 5) := by
      apply dvd_mul_of_dvd_right; have := dvd_sub e1 e2; convert this using 1; ring
    have e4 : lam ^ 3 ∣ (ε : 𝓞 K5) * ((b : 𝓞 K5) * 125) :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_right lam_pow_three_dvd_125 _) _
    have hab' : (a : 𝓞 K5) * (cs : 𝓞 K5) ^ 5 + (b : 𝓞 K5) * 125 = 1 := by exact_mod_cast hab
    have := dvd_add e3 e4
    convert this using 1; push_cast; linear_combination (-(ε : 𝓞 K5)) * hab'
  obtain ⟨η, hη⟩ := kummer_lemma ε _ hεc
  -- apply the induction hypothesis
  apply IH j0 tr (η * ts) w0 E2 hltr (not_lam_dvd_mul (not_lam_dvd_unit η) hlts) hlw0
  · have h1 : IsCoprime (tr ^ 5) (ts ^ 5) := by
      have := hcrs; rw [her, hes] at this
      exact ((isCoprime_mul_unit_left_left er.isUnit _ _).mp
        ((isCoprime_mul_unit_left_right es.isUnit _ _).mp this))
    have h2 : IsCoprime tr ts := IsCoprime.of_isCoprime_of_dvd_left
      (IsCoprime.of_isCoprime_of_dvd_right h1 (dvd_pow_self ts (by norm_num))) (dvd_pow_self tr (by norm_num))
    exact (isCoprime_mul_unit_left_right η.isUnit _ _).mpr h2
  · rw [show 5 * (μ - 1) + 5 = 5 * μ by omega, mul_pow, ← Units.val_pow_eq_pow_val, ← hη]
    exact hnew

/-- Pick a fifth-power decomposition for a factor coprime to its cofactor. -/
lemma pick_fifth {γ R w : 𝓞 K5} {E : (𝓞 K5)ˣ} {j : ℕ} (hcop : IsCoprime γ R) (h2 : ¬ (2 : 𝓞 K5) ∣ γ)
    (h : γ * R = E * 2 ^ j * w ^ 5) : ∃ e : (𝓞 K5)ˣ, ∃ t : 𝓞 K5, γ = e * t ^ 5 := by
  obtain ⟨t, e, he⟩ := fifth_of_coprime hcop h2 h
  exact ⟨e, t, he⟩

/-- **Maillet's lemma** for `l = 5` and `A = 2^j`. -/
theorem maillet (μ : ℕ) : ∀ (j : ℕ) (u v w : 𝓞 K5) (E : (𝓞 K5)ˣ), ¬ lam ∣ u → ¬ lam ∣ v →
    ¬ lam ∣ w → IsCoprime u v → u ^ 5 + v ^ 5 = E * lam ^ (5 * μ + 5) * 2 ^ j * w ^ 5 → False := by
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
  intro j u0 v0 w E hu0 hv0 hw hcop0 heq0
  obtain ⟨k1, a, hua⟩ := normalize hu0
  obtain ⟨k2, b, hvb⟩ := normalize hv0
  set u := ζ ^ k1 * u0 with hudef
  set v := ζ ^ k2 * v0 with hvdef
  have hζu : ∀ k : ℕ, IsUnit (ζ ^ k) := fun k => (hζ5.toInteger_isPrimitiveRoot.isUnit (by norm_num)).pow k
  have hp5 : ∀ (k : ℕ) (x : 𝓞 K5), (ζ ^ k * x) ^ 5 = x ^ 5 := fun k x => by
    rw [mul_pow, ← pow_mul, mul_comm k 5, pow_mul, ζ_pow_five, one_pow, one_mul]
  have heq : u ^ 5 + v ^ 5 = E * lam ^ (5 * μ + 5) * 2 ^ j * w ^ 5 := by rw [hudef, hvdef, hp5, hp5]; exact heq0
  have hu : ¬ lam ∣ u := not_lam_dvd_mul (by obtain ⟨U, hU⟩ := hζu k1; rw [← hU]; exact not_lam_dvd_unit U) hu0
  have hv : ¬ lam ∣ v := not_lam_dvd_mul (by obtain ⟨U, hU⟩ := hζu k2; rw [← hU]; exact not_lam_dvd_unit U) hv0
  have hcop : IsCoprime u v :=
    (isCoprime_mul_unit_left_left (hζu k1) _ _).mpr ((isCoprime_mul_unit_left_right (hζu k2) _ _).mpr hcop0)
  clear_value u v
  -- λ² ∣ u + v
  have hl5 : lam ∣ u ^ 5 + v ^ 5 := by
    rw [heq]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
      (dvd_pow_self lam (by omega)) _) _) _
  have hab5 : lam ∣ ((a ^ 5 + b ^ 5 : ℤ) : 𝓞 K5) := by
    have e1 := dvd_trans (dvd_pow_self lam (by norm_num : 2 ≠ 0)) (pow_congr 5 hua)
    have e2 := dvd_trans (dvd_pow_self lam (by norm_num : 2 ≠ 0)) (pow_congr 5 hvb)
    have := dvd_sub (dvd_sub hl5 e1) e2
    push_cast; convert this using 1; ring
  have hab : (5 : ℤ) ∣ a + b := five_dvd_add_of_pow (lam_dvd_int hab5)
  have h2uv : lam ^ 2 ∣ u + v := by
    have := dvd_add (dvd_add hua hvb) (lam_pow_dvd_of_five_dvd hab (j := 2) (by norm_num))
    convert this using 1; push_cast; ring
  -- the four factors
  obtain ⟨γ1, h1, hl1⟩ := factor_i hv h2uv 1 (by norm_num)
  obtain ⟨γ2, h2, hl2⟩ := factor_i hv h2uv 2 (by norm_num)
  obtain ⟨γ3, h3, hl3⟩ := factor_i hv h2uv 3 (by norm_num)
  obtain ⟨γ4, h4, hl4⟩ := factor_i hv h2uv 4 (by norm_num)
  have h1' := h1
  rw [pow_one] at h1'
  set Γ := γ1 * γ2 * γ3 * γ4 with hΓ
  have hlΓ : ¬ lam ∣ Γ := not_lam_dvd_mul (not_lam_dvd_mul (not_lam_dvd_mul hl1 hl2) hl3) hl4
  have hprod : (u + v) * Γ = E * lam ^ (5 * μ + 1) * 2 ^ j * w ^ 5 := by
    have hp := prod_five u v
    rw [h1', h2, h3, h4, heq] at hp
    apply mul_left_cancel₀ (pow_ne_zero 4 lam_ne_zero)
    rw [hΓ]; linear_combination hp
  have hcopL : IsCoprime (lam ^ (5 * μ + 1)) Γ :=
    ((Prime.coprime_iff_not_dvd lam_prime).mpr hlΓ).pow_left
  obtain ⟨γ0, h0⟩ : lam ^ (5 * μ + 1) ∣ u + v :=
    hcopL.dvd_of_dvd_mul_right ⟨E * 2 ^ j * w ^ 5, by rw [hprod]; ring⟩
  have hprod0 : γ0 * Γ = E * 2 ^ j * w ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero (5 * μ + 1) lam_ne_zero)
    rw [← mul_assoc, ← h0, hprod]; ring
  have hl0 : ¬ lam ∣ γ0 := by
    intro hl
    have : lam ∣ (E : 𝓞 K5) * 2 ^ j * w ^ 5 := by rw [← hprod0]; exact dvd_mul_of_dvd_left hl _
    exact not_lam_dvd_mul (not_lam_dvd_mul (not_lam_dvd_unit E) (not_lam_dvd_two_pow j))
      (not_lam_dvd_pow hw 5) this
  -- base case μ = 0
  rcases Nat.eq_zero_or_pos μ with hμ0 | hμ
  · subst hμ0
    apply hl0
    rw [h0] at h2uv
    simpa using lam_cancel (j := 1) (by simpa [pow_succ] using h2uv)
  -- pairwise coprimality
  have cq : ∀ {r s : ℕ} {X Y : 𝓞 K5}, r < s → s < 5 → u + ζ ^ r * v = lam * X →
      u + ζ ^ s * v = lam * Y → IsCoprime X Y := fun hrs hs hX hY => by
    obtain ⟨w', hw', he'⟩ := diff_eq hrs hs
    exact coprime_quot hcop hX hY he' hw'
  have h0' : u + ζ ^ 0 * v = lam * (lam ^ (5 * μ) * γ0) := by rw [pow_zero, one_mul, h0]; ring
  have c12 := cq (by norm_num) (by norm_num) h1 h2
  have c13 := cq (by norm_num) (by norm_num) h1 h3
  have c14 := cq (by norm_num) (by norm_num) h1 h4
  have c23 := cq (by norm_num) (by norm_num) h2 h3
  have c24 := cq (by norm_num) (by norm_num) h2 h4
  have c34 := cq (by norm_num) (by norm_num) h3 h4
  have c0 : ∀ {s : ℕ} {Y : 𝓞 K5}, 1 ≤ s → s < 5 → u + ζ ^ s * v = lam * Y → IsCoprime γ0 Y :=
    fun hs1 hs5 hY => (cq (by omega) hs5 h0' hY).of_mul_left_right
  have c01 := c0 (by norm_num) (by norm_num) h1
  have c02 := c0 (by norm_num) (by norm_num) h2
  have c03 := c0 (by norm_num) (by norm_num) h3
  have c04 := c0 (by norm_num) (by norm_num) h4
  -- decompose γ0 = 2^j0 * g0
  have hγ0ne : γ0 ≠ 0 := by rintro rfl; exact hl0 (dvd_zero _)
  obtain ⟨g0, hg0, hg02⟩ :=
    (FiniteMultiplicity.of_not_isUnit two_prime.not_unit hγ0ne).exists_eq_pow_mul_and_not_dvd
  set j0 := multiplicity (2 : 𝓞 K5) γ0
  have hcopg : IsCoprime g0 (2 ^ j0 * Γ) := by
    have hg2 : IsCoprime g0 (2 ^ j0) := ((Prime.coprime_iff_not_dvd two_prime).mpr hg02).symm.pow_right
    have hgdvd : g0 ∣ γ0 := ⟨2 ^ j0, by rw [hg0]; ring⟩
    have hgΓ : IsCoprime g0 Γ := by
      have := ((c01.mul_right c02).mul_right c03).mul_right c04
      exact this.of_isCoprime_of_dvd_left hgdvd
    exact hg2.mul_right hgΓ
  obtain ⟨e0, w0, he0⟩ := pick_fifth hcopg hg02 (by rw [← hprod0, hg0]; ring)
  have he0' : γ0 = 2 ^ j0 * (e0 * w0 ^ 5) := by rw [hg0, he0]
  have IH : ∀ (j : ℕ) (u v w : 𝓞 K5) (E : (𝓞 K5)ˣ), ¬ lam ∣ u → ¬ lam ∣ v → ¬ lam ∣ w →
      IsCoprime u v → u ^ 5 + v ^ 5 = E * lam ^ (5 * (μ - 1) + 5) * 2 ^ j * w ^ 5 → False :=
    ih (μ - 1) (by omega)
  -- choose a pair of odd factors
  have h2u : ¬ IsUnit (2 : 𝓞 K5) := two_prime.not_unit
  by_cases d1 : (2 : 𝓞 K5) ∣ γ1
  · have d2 : ¬ (2 : 𝓞 K5) ∣ γ2 := fun d => h2u (c12.isUnit_of_dvd' d1 d)
    have d3 : ¬ (2 : 𝓞 K5) ∣ γ3 := fun d => h2u (c13.isUnit_of_dvd' d1 d)
    obtain ⟨er, tr, her⟩ := pick_fifth (((c12.symm.mul_right c23).mul_right c24).mul_right c02.symm) d2
      (by rw [← hprod0, hΓ]; ring)
    obtain ⟨es, ts, hes⟩ := pick_fifth (((c13.symm.mul_right c23.symm).mul_right c34).mul_right c03.symm) d3
      (by rw [← hprod0, hΓ]; ring)
    exact maillet_finish hμ IH (by norm_num : 2 < 3) (by norm_num) (by norm_num) h0 h2 h3 c23 hl2 hl3 hl0
      her hes he0'
  · by_cases d2 : (2 : 𝓞 K5) ∣ γ2
    · have d3 : ¬ (2 : 𝓞 K5) ∣ γ3 := fun d => h2u (c23.isUnit_of_dvd' d2 d)
      obtain ⟨er, tr, her⟩ := pick_fifth (((c12.mul_right c13).mul_right c14).mul_right c01.symm) d1
        (by rw [← hprod0, hΓ]; ring)
      obtain ⟨es, ts, hes⟩ := pick_fifth (((c13.symm.mul_right c23.symm).mul_right c34).mul_right c03.symm) d3
        (by rw [← hprod0, hΓ]; ring)
      exact maillet_finish hμ IH (by norm_num : 1 < 3) (by norm_num) (by norm_num) h0 h1 h3 c13 hl1 hl3 hl0
        her hes he0'
    · obtain ⟨er, tr, her⟩ := pick_fifth (((c12.mul_right c13).mul_right c14).mul_right c01.symm) d1
        (by rw [← hprod0, hΓ]; ring)
      obtain ⟨es, ts, hes⟩ := pick_fifth (((c12.symm.mul_right c23).mul_right c24).mul_right c02.symm) d2
        (by rw [← hprod0, hΓ]; ring)
      exact maillet_finish hμ IH (by norm_num : 1 < 2) (by norm_num) (by norm_num) h0 h1 h2 c12 hl1 hl2 hl0
        her hes he0'

/-- **Case c** (Dénes): no coprime solution of `x^5 + y^5 = 2^j z^5` with `5 ∣ z`, `z ≠ 0`. -/
theorem case_c {x y z : ℤ} {j : ℕ} (h : x ^ 5 + y ^ 5 = 2 ^ j * z ^ 5)
    (hxy : IsCoprime x y) (hz5 : (5 : ℤ) ∣ z) (hz0 : z ≠ 0) : False := by
  have hp : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  have h5u : ¬ IsUnit (5 : ℤ) := hp.not_unit
  -- x, y prime to 5
  have hx5 : ¬ (5 : ℤ) ∣ x := by
    intro hx
    have : (5 : ℤ) ∣ y ^ 5 := by
      have : y ^ 5 = 2 ^ j * z ^ 5 - x ^ 5 := by linarith
      rw [this]; exact dvd_sub (dvd_mul_of_dvd_right (dvd_pow hz5 (by norm_num)) _) (dvd_pow hx (by norm_num))
    exact h5u (hxy.isUnit_of_dvd' hx (hp.dvd_of_dvd_pow this))
  have hy5 : ¬ (5 : ℤ) ∣ y := by
    intro hy
    have : (5 : ℤ) ∣ x ^ 5 := by
      have : x ^ 5 = 2 ^ j * z ^ 5 - y ^ 5 := by linarith
      rw [this]; exact dvd_sub (dvd_mul_of_dvd_right (dvd_pow hz5 (by norm_num)) _) (dvd_pow hy (by norm_num))
    exact h5u (hxy.isUnit_of_dvd' (hp.dvd_of_dvd_pow this) hy)
  -- z = 5^k z1
  obtain ⟨z1, hz, hz1⟩ := (FiniteMultiplicity.of_not_isUnit h5u hz0).exists_eq_pow_mul_and_not_dvd
  set k := multiplicity (5 : ℤ) z
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, pow_zero, one_mul] at hz; exact absurd (hz ▸ hz5) hz1
    · exact h0
  have hlx : ¬ lam ∣ (x : 𝓞 K5) := fun hl => hx5 (lam_dvd_int hl)
  have hly : ¬ lam ∣ (y : 𝓞 K5) := fun hl => hy5 (lam_dvd_int hl)
  have hlz : ¬ lam ∣ (z1 : 𝓞 K5) := fun hl => hz1 (lam_dvd_int hl)
  have hcop : IsCoprime (x : 𝓞 K5) (y : 𝓞 K5) := hxy.map (Int.castRingHom (𝓞 K5))
  apply maillet (4 * k - 1) j x y z1 (u5_isUnit.unit ^ (5 * k)) hlx hly hlz hcop
  have hO : ((x : 𝓞 K5)) ^ 5 + (y : 𝓞 K5) ^ 5 = 2 ^ j * ((5 : 𝓞 K5) ^ k * z1) ^ 5 := by
    have := congrArg (fun t : ℤ => (t : 𝓞 K5)) h
    rw [hz] at this; push_cast at this; exact this
  rw [hO, ← five_eq]
  have e : 5 * (4 * k - 1) + 5 = 4 * (5 * k) := by omega
  rw [e, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  generalize lam = L; generalize u5 = U; ring

end CaseC

end OMA672Z5



-- ===== Eis2.lean =====

open NumberField Polynomial

namespace OMA672Z5

noncomputable abbrev pb5 := hζ5.integralPowerBasis

lemma pb5_gen : pb5.gen = ζ := IsPrimitiveRoot.integralPowerBasis_gen _

lemma ζ_prim : IsPrimitiveRoot ζ 5 := hζ5.toInteger_isPrimitiveRoot

lemma aeval_minpoly_pow {c : ℕ} (hc : Nat.Coprime c 5) : aeval (ζ ^ c) (minpoly ℤ pb5.gen) = 0 := by
  have hm : minpoly ℤ ζ = cyclotomic 5 ℤ := by
    rw [cyclotomic_eq_minpoly hζ5 (by norm_num), ← minpoly.algebraMap_eq
      (RingOfIntegers.coe_injective (K := K5)) ζ]
    rfl
  rw [pb5_gen, hm]
  have := (ζ_prim.pow_of_coprime c hc).isRoot_cyclotomic (by norm_num)
  rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]; exact this

/-- The Galois automorphism `ζ ↦ ζ^c`. -/
noncomputable def τ (c : ℕ) (hc : Nat.Coprime c 5) : 𝓞 K5 →+* 𝓞 K5 :=
  (pb5.lift (ζ ^ c) (aeval_minpoly_pow hc)).toRingHom

lemma τ_ζ {c : ℕ} (hc : Nat.Coprime c 5) : τ c hc ζ = ζ ^ c := by
  have := pb5.lift_gen (ζ ^ c) (aeval_minpoly_pow hc)
  rw [pb5_gen] at this; exact this

lemma ringHom_ext {f g : 𝓞 K5 →+* 𝓞 K5} (h : f ζ = g ζ) : f = g := by
  ext x
  obtain ⟨a, b, c, e, rfl⟩ := exists_coord x
  simp [h]

lemma τ_comp {a b : ℕ} (ha : Nat.Coprime a 5) (hb : Nat.Coprime b 5) (hab : Nat.Coprime (a * b) 5) :
    (τ a ha).comp (τ b hb) = τ (a * b) hab := by
  apply ringHom_ext
  simp only [RingHom.comp_apply, τ_ζ, map_pow]; ring

lemma τ_one : τ 1 (by norm_num) = RingHom.id _ := by
  apply ringHom_ext; simp [τ_ζ]

lemma ζ_pow_mod (n : ℕ) : ζ ^ n = ζ ^ (n % 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, ζ_pow_five, one_pow, mul_one]

lemma τ_six : τ 6 (by norm_num) = RingHom.id _ := by
  apply ringHom_ext; simp [τ_ζ]; rw [ζ_pow_mod]; norm_num

lemma τ_four_eq_σ (x : 𝓞 K5) : τ 4 (by norm_num) x = σ x := by
  have : τ 4 (by norm_num) = (σ : 𝓞 K5 →+* 𝓞 K5) := by
    apply ringHom_ext; rw [τ_ζ]; exact (σ_ζ).symm
  rw [this]; rfl

section Frob

lemma two_dvd_sq_sub_sq {a b : 𝓞 K5} (h : (2 : 𝓞 K5) ∣ a - b) : (2 : 𝓞 K5) ∣ a ^ 2 - b ^ 2 := by
  have : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [this]; exact dvd_mul_of_dvd_left h _

lemma int_sq_sub (n : ℤ) : ∃ t : ℤ, n ^ 2 - n = 2 * t := by
  obtain ⟨t, ht⟩ := Int.even_mul_pred_self n
  exact ⟨t, by linear_combination ht⟩

/-- Frobenius mod 2: `x² ≡ τ₂ x`. -/
lemma frob2 (x : 𝓞 K5) : (2 : 𝓞 K5) ∣ x ^ 2 - τ 2 (by norm_num) x := by
  obtain ⟨a, b, c, e, rfl⟩ := exists_coord x
  obtain ⟨ta, hta⟩ := int_sq_sub a
  obtain ⟨tb, htb⟩ := int_sq_sub b
  obtain ⟨tc, htc⟩ := int_sq_sub c
  obtain ⟨te, hte⟩ := int_sq_sub e
  have hτ : τ 2 (by norm_num) ((a : 𝓞 K5) + b * ζ + c * ζ ^ 2 + e * ζ ^ 3)
      = a + b * ζ ^ 2 + c * ζ ^ 4 + e * ζ ^ 6 := by
    simp only [map_add, map_mul, map_intCast, map_pow, τ_ζ]; ring
  rw [hτ]
  refine ⟨ta + tb * ζ ^ 2 + tc * ζ ^ 4 + te * ζ ^ 6 + (a * b * ζ + a * c * ζ ^ 2 + a * e * ζ ^ 3
    + b * c * ζ ^ 3 + b * e * ζ ^ 4 + c * e * ζ ^ 5), ?_⟩
  have e1 : ((a : 𝓞 K5)) ^ 2 - a = 2 * ta := by exact_mod_cast hta
  have e2 : ((b : 𝓞 K5)) ^ 2 - b = 2 * tb := by exact_mod_cast htb
  have e3 : ((c : 𝓞 K5)) ^ 2 - c = 2 * tc := by exact_mod_cast htc
  have e4 : ((e : 𝓞 K5)) ^ 2 - e = 2 * te := by exact_mod_cast hte
  linear_combination e1 + ζ ^ 2 * e2 + ζ ^ 4 * e3 + ζ ^ 6 * e4

lemma τ_two_dvd {c : ℕ} (hc : Nat.Coprime c 5) {a b : 𝓞 K5} (h : (2 : 𝓞 K5) ∣ a - b) :
    (2 : 𝓞 K5) ∣ τ c hc a - τ c hc b := by
  obtain ⟨t, ht⟩ := h
  exact ⟨τ c hc t, by rw [← map_sub, ht, map_mul, map_ofNat]⟩

lemma frob_step {n : ℕ} (hn : Nat.Coprime n 5) (h2n : Nat.Coprime (2 * n) 5) (m : ℕ)
    (H : ∀ x : 𝓞 K5, (2 : 𝓞 K5) ∣ x ^ m - τ n hn x) (x : 𝓞 K5) :
    (2 : 𝓞 K5) ∣ x ^ (2 * m) - τ (2 * n) h2n x := by
  have h1 : (2 : 𝓞 K5) ∣ (x ^ m) ^ 2 - (τ n hn x) ^ 2 := two_dvd_sq_sub_sq (H x)
  have h2 := frob2 (τ n hn x)
  have h3 : τ 2 (by norm_num) (τ n hn x) = τ (2 * n) h2n x := by
    rw [← RingHom.comp_apply, τ_comp]
  rw [h3] at h2
  have := dvd_add h1 h2
  rw [show x ^ (2 * m) = (x ^ m) ^ 2 by ring]
  convert this using 1; ring

lemma τ_mod {a b : ℕ} (ha : Nat.Coprime a 5) (hb : Nat.Coprime b 5) (h : a % 5 = b % 5) :
    τ a ha = τ b hb := by
  apply ringHom_ext; rw [τ_ζ, τ_ζ, ζ_pow_mod a, ζ_pow_mod b, h]

lemma frob4 (x : 𝓞 K5) : (2 : 𝓞 K5) ∣ x ^ 4 - σ x := by
  have := frob_step (n := 2) (by norm_num) (by norm_num) 2 frob2 x
  rw [τ_four_eq_σ] at this; simpa using this

lemma frob8 (x : 𝓞 K5) : (2 : 𝓞 K5) ∣ x ^ 8 - τ 3 (by norm_num) x := by
  have h4 : ∀ y : 𝓞 K5, (2 : 𝓞 K5) ∣ y ^ 4 - τ 4 (by norm_num) y :=
    frob_step (n := 2) (by norm_num) (by norm_num) 2 frob2
  have := frob_step (n := 4) (by norm_num) (by norm_num) 4 h4 x
  rwa [τ_mod (a := 2 * 4) (b := 3) (by norm_num) (by norm_num) (by norm_num)] at this

lemma frob16 (x : 𝓞 K5) : (2 : 𝓞 K5) ∣ x ^ 16 - x := by
  have h4 : ∀ y : 𝓞 K5, (2 : 𝓞 K5) ∣ y ^ 4 - τ 4 (by norm_num) y :=
    frob_step (n := 2) (by norm_num) (by norm_num) 2 frob2
  have h8 : ∀ y : 𝓞 K5, (2 : 𝓞 K5) ∣ y ^ 8 - τ 8 (by norm_num) y :=
    frob_step (n := 4) (by norm_num) (by norm_num) 4 h4
  have := frob_step (n := 8) (by norm_num) (by norm_num) 8 h8 x
  rwa [τ_mod (a := 2 * 8) (b := 1) (by norm_num) (by norm_num) (by norm_num), τ_one] at this

end Frob

section Char

variable {p : ℕ} [hp : Fact p.Prime] (ψ : 𝓞 K5 →+* ZMod p) (hd : ψ ζ ≠ 1)

include hd in
lemma d_prim : IsPrimitiveRoot (ψ ζ) 5 := by
  have h5 : (ψ ζ) ^ 5 = 1 := by rw [← map_pow, ζ_pow_five, map_one]
  have := orderOf_eq_prime (p := 5) h5 hd
  have h := IsPrimitiveRoot.orderOf (ψ ζ)
  rwa [this] at h

lemma ζ_pow_eq_of_mod {a b : ℕ} (h : a % 5 = b % 5) : ζ ^ a = ζ ^ b := by
  rw [ζ_pow_mod a, ζ_pow_mod b, h]

include hd in
lemma ζ_inj {a b : ℕ} (h : ψ ζ ^ a = ψ ζ ^ b) : ζ ^ a = ζ ^ b := by
  have hdp := d_prim ψ hd
  have hd0 : ψ ζ ≠ 0 := hdp.ne_zero (by norm_num)
  apply ζ_pow_eq_of_mod
  rcases le_total b a with hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add] at h
    have : ψ ζ ^ c = 1 := by
      have := mul_left_cancel₀ (pow_ne_zero b hd0) (h.trans (mul_one _).symm); exact this
    have := (hdp.pow_eq_one_iff_dvd c).mp this
    omega
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add] at h
    have : ψ ζ ^ c = 1 := by
      have := mul_left_cancel₀ (pow_ne_zero a hd0) (h.symm.trans (mul_one _).symm); exact this
    have := (hdp.pow_eq_one_iff_dvd c).mp this
    omega

include hd in
lemma five_dvd_p_sub_one : 5 ∣ p - 1 := by
  have hdp := d_prim ψ hd
  have := ZMod.orderOf_dvd_card_sub_one (hdp.ne_zero (by norm_num))
  rwa [← hdp.eq_orderOf] at this

/-- `k = (p - 1) / 5`. -/
abbrev kk (p : ℕ) : ℕ := (p - 1) / 5

include hd in
lemma five_kk : 5 * kk p = p - 1 := Nat.mul_div_cancel' (five_dvd_p_sub_one ψ hd)

include hd in
lemma pow_kk_root {t : ZMod p} (ht : t ≠ 0) : (t ^ kk p) ^ 5 = 1 := by
  rw [← pow_mul, mul_comm, five_kk ψ hd]; exact ZMod.pow_card_sub_one_eq_one ht

include hd in
lemma exists_idx (u : (ZMod p)ˣ) : ∃ i : ℕ, ψ ζ ^ i = (u : ZMod p) ^ kk p := by
  obtain ⟨i, -, h⟩ := (d_prim ψ hd).eq_pow_of_pow_eq_one (pow_kk_root ψ hd u.ne_zero)
  exact ⟨i, h⟩

/-- The index of `u^k` with respect to `ψ ζ`. -/
noncomputable def idx (u : (ZMod p)ˣ) : ℕ := Classical.choose (exists_idx ψ hd u)

lemma idx_spec (u : (ZMod p)ˣ) : ψ ζ ^ idx ψ hd u = (u : ZMod p) ^ kk p :=
  Classical.choose_spec (exists_idx ψ hd u)

/-- The unit homomorphism behind the quintic character. -/
noncomputable def χh : (ZMod p)ˣ →* (𝓞 K5)ˣ where
  toFun u := ζu ^ idx ψ hd u
  map_one' := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    have : ζ ^ idx ψ hd 1 = ζ ^ 0 := ζ_inj ψ hd (by rw [idx_spec]; simp)
    simpa using this
  map_mul' u v := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec]
    rw [← pow_add]
    apply ζ_inj ψ hd
    rw [pow_add, idx_spec, idx_spec, idx_spec, Units.val_mul, mul_pow]

/-- The quintic residue character attached to `ψ`. -/
noncomputable def χ5 : MulChar (ZMod p) (𝓞 K5) := MulChar.ofUnitHom (χh ψ hd)

lemma χ5_unit (u : (ZMod p)ˣ) : χ5 ψ hd u = ζ ^ idx ψ hd u := by
  simp [χ5, MulChar.ofUnitHom_coe, χh]

include hd in
lemma kk_pos : 0 < kk p := by
  have h5 := five_kk ψ hd
  have : 2 ≤ p := hp.out.two_le
  have : p ≠ 1 + 1 ∨ True := Or.inr trivial
  rcases Nat.eq_zero_or_pos (kk p) with h | h
  · exfalso; rw [h] at h5
    have h6 : p = 1 := by omega
    exact hd (by
      have := (d_prim ψ hd).pow_eq_one; subst h6
      exact Subsingleton.elim _ _)
  · exact h

lemma ψ_χ5 (t : ZMod p) : ψ (χ5 ψ hd t) = t ^ kk p := by
  by_cases ht : t = 0
  · subst ht
    rw [MulChar.map_zero, map_zero, zero_pow (kk_pos ψ hd).ne']
  · have hu : IsUnit t := isUnit_iff_ne_zero.mpr ht
    rw [← hu.unit_spec, χ5_unit, map_pow, idx_spec]

lemma χ5_cases (t : ZMod p) : χ5 ψ hd t = 0 ∨ ∃ i : ℕ, χ5 ψ hd t = ζ ^ i := by
  by_cases ht : t = 0
  · left; subst ht; exact MulChar.map_zero _
  · right; have hu : IsUnit t := isUnit_iff_ne_zero.mpr ht
    rw [← hu.unit_spec, χ5_unit]; exact ⟨_, rfl⟩

lemma τ_χ5 {c : ℕ} (hc : Nat.Coprime c 5) (hc0 : c ≠ 0) (t : ZMod p) :
    τ c hc (χ5 ψ hd t) = (χ5 ψ hd t) ^ c := by
  rcases χ5_cases ψ hd t with h | ⟨i, h⟩
  · rw [h, map_zero, zero_pow hc0]
  · rw [h, map_pow, τ_ζ, ← pow_mul, ← pow_mul, mul_comm]

include hd in
lemma p_ne_two : p ≠ 2 := by
  have := five_dvd_p_sub_one ψ hd; intro h; subst h; norm_num at this

lemma sum_vanish (m : ℕ) (hm : 2 * m < p - 1) : ∑ x : ZMod p, x ^ m * (1 - x) ^ m = 0 := by
  have hq : Fintype.card (ZMod p) = p := ZMod.card p
  have e : ∀ x : ZMod p, x ^ m * (1 - x) ^ m =
      ∑ j ∈ Finset.range (m + 1), ((-1) ^ j * (m.choose j : ZMod p)) * x ^ (m + j) := by
    intro x
    rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [one_pow, mul_one, neg_pow, pow_add]; ring
  simp_rw [e]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro j hj
  rw [← Finset.mul_sum]
  have hj' : j < m + 1 := Finset.mem_range.mp hj
  have := FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) (m + j) (by rw [hq]; omega)
  rw [this, mul_zero]

/-- The Jacobi sum `J(χ, χ)`. -/
noncomputable abbrev JJ : 𝓞 K5 := jacobiSum (χ5 ψ hd) (χ5 ψ hd)

include hd in
lemma ψ_JJ : ψ (JJ ψ hd) = 0 := by
  rw [JJ, jacobiSum, map_sum]
  simp_rw [map_mul, ψ_χ5]
  apply sum_vanish
  have := five_kk ψ hd; have := kk_pos ψ hd; omega

include hd in
lemma ψ_τ2_JJ : ψ (τ 2 (by norm_num) (JJ ψ hd)) = 0 := by
  rw [JJ, jacobiSum, map_sum, map_sum]
  simp_rw [map_mul, τ_χ5 ψ hd (c := 2) (by norm_num) (by norm_num), map_pow, ψ_χ5, ← pow_mul, ← mul_pow]
  simp_rw [mul_pow]
  apply sum_vanish
  have := five_kk ψ hd; have := kk_pos ψ hd; omega

include hd in
lemma χ5_two_inv_sq_mod2 :
    (2 : 𝓞 K5) ∣ JJ ψ hd - (χ5 ψ hd (2⁻¹)) ^ 2 := by
  have hp2 := p_ne_two ψ hd
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have hh : (1 : ZMod p) - 2⁻¹ = 2⁻¹ := by
    field_simp; ring
  set f : ZMod p → 𝓞 K5 := fun x => χ5 ψ hd x * χ5 ψ hd (1 - x) with hf
  let mk := Ideal.Quotient.mk (Ideal.span {(2 : 𝓞 K5)})
  have key : ∑ x ∈ Finset.univ.erase (2⁻¹ : ZMod p), mk (f x) = 0 := by
    refine Finset.sum_involution (fun x _ => 1 - x) ?_ ?_ ?_ ?_
    · intro a _
      have : f (1 - a) = f a := by simp only [hf, sub_sub_cancel]; ring
      rw [this, ← map_add, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact ⟨f a, by ring⟩
    · intro a ha _ h
      apply (Finset.mem_erase.mp ha).1
      have : 2 * a = 1 := by linear_combination -h
      field_simp; linear_combination this
    · intro a ha
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h; apply (Finset.mem_erase.mp ha).1
      rw [← hh]; linear_combination -h
    · intro a _; ring
  have hJ : mk (JJ ψ hd) = mk (f 2⁻¹) := by
    rw [JJ, jacobiSum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (2⁻¹ : ZMod p)), key,
      add_zero]
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, hJ, hf]
  simp only [hh, pow_two]; exact sub_self _

include hd in
lemma JJ_primary : lam ^ 2 ∣ JJ ψ hd + 1 := by
  have h5 : χ5 ψ hd ^ 5 = 1 := by
    apply MulChar.ext; intro u
    rw [MulChar.pow_apply_coe, χ5_unit, MulChar.one_apply_coe, ← pow_mul, mul_comm, pow_mul,
      ζ_pow_five, one_pow]
  have hc : 5 ∣ Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; exact five_dvd_p_sub_one ψ hd
  obtain ⟨z, -, hz⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num : 2 < 5) h5 h5 hc ζ_prim
  refine ⟨z, ?_⟩
  rw [JJ, hz]; ring

lemma χ5_inv (x : ZMod p) : χ5 ψ hd x⁻¹ = σ (χ5 ψ hd x) := by
  by_cases hx : x = 0
  · subst hx; rw [inv_zero, MulChar.map_zero, map_zero]
  · rcases χ5_cases ψ hd x with h | ⟨i, h⟩
    · exfalso
      have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
      rw [← hu.unit_spec, χ5_unit] at h
      exact pow_ne_zero _ (fun h0 => by simpa [h0] using ζ_pow_five) h
    · have h1 : χ5 ψ hd x⁻¹ * χ5 ψ hd x = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hx, MulChar.map_one]
      have h2 : σ (χ5 ψ hd x) * χ5 ψ hd x = 1 := by
        rw [h, map_pow, σ_ζ, ← pow_mul, ← pow_add, show 4 * i + i = 5 * i by ring, pow_mul,
          ζ_pow_five, one_pow]
      calc χ5 ψ hd x⁻¹ = χ5 ψ hd x⁻¹ * (σ (χ5 ψ hd x) * χ5 ψ hd x) := by rw [h2, mul_one]
        _ = σ (χ5 ψ hd x) * (χ5 ψ hd x⁻¹ * χ5 ψ hd x) := by ring
        _ = σ (χ5 ψ hd x) := by rw [h1, mul_one]

lemma exists_gen_pow_ne_one :
    ∃ g : ZMod p, g ≠ 0 ∧ ∀ n, 0 < n → n < p - 1 → g ^ n ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hc : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  refine ⟨g, g.ne_zero, fun n hn0 hn h => ?_⟩
  have : g ^ n = 1 := Units.ext (by simpa using h)
  have := orderOf_le_of_pow_eq_one hn0 this
  omega

include hd in
lemma JJ_mul_σ : JJ ψ hd * σ (JJ ψ hd) = p := by
  set f := algebraMap (𝓞 K5) K5
  have hfi : Function.Injective f := RingOfIntegers.coe_injective
  set χ' := (χ5 ψ hd).ringHomComp f
  have hk := five_kk ψ hd; have hk0 := kk_pos ψ hd
  obtain ⟨g, hg0, hg⟩ := exists_gen_pow_ne_one (p := p)
  have hχ1 : χ' ≠ 1 := by
    intro h
    have : χ' g = 1 := by
      rw [h]; exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hg0)
    have h2 : χ5 ψ hd g = 1 := hfi (by simpa [χ'] using this)
    have := congrArg ψ h2; rw [ψ_χ5, map_one] at this
    exact hg (kk p) hk0 (by omega) this
  have hχ2 : χ' * χ' ≠ 1 := by
    intro h
    have : (χ' * χ') g = 1 := by
      rw [h]; exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hg0)
    rw [MulChar.mul_apply] at this
    have h2 : χ5 ψ hd g * χ5 ψ hd g = 1 := hfi (by simpa [χ'] using this)
    have := congrArg ψ h2; rw [map_mul, ψ_χ5, map_one, ← pow_add] at this
    exact hg (kk p + kk p) (by omega) (by omega) this
  have hch : ringChar K5 ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact hp.out.ne_zero.symm
  have key := jacobiSum_mul_jacobiSum_inv hch hχ1 hχ1 hχ2
  rw [jacobiSum_ringHomComp] at key
  have hinv : jacobiSum χ'⁻¹ χ'⁻¹ = f (σ (JJ ψ hd)) := by
    simp only [jacobiSum, MulChar.inv_apply', χ', MulChar.ringHomComp_apply, map_sum, map_mul,
      χ5_inv, JJ]
  rw [hinv, ← map_mul, ZMod.card] at key
  exact hfi (by rw [key]; simp [f])

lemma finrank_O : Module.finrank ℤ (𝓞 K5) = 4 := by
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  rw [NumberField.RingOfIntegers.rank, IsCyclotomicExtension.finrank (n := 5) K5
    (cyclotomic.irreducible_rat (by norm_num)), Nat.totient_prime Nat.prime_five]

lemma absNorm_equiv (e : 𝓞 K5 ≃+* 𝓞 K5) (x : 𝓞 K5) :
    Ideal.absNorm (Ideal.span {e x}) = Ideal.absNorm (Ideal.span {x}) := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)).toEquiv.symm

lemma τ32 (x : 𝓞 K5) : τ 3 (by norm_num) (τ 2 (by norm_num) x) = x := by
  rw [← RingHom.comp_apply, τ_comp (hab := by norm_num),
    τ_mod (a := 3 * 2) (b := 1) (by norm_num) (by norm_num) (by norm_num), τ_one]; rfl

lemma τ23 (x : 𝓞 K5) : τ 2 (by norm_num) (τ 3 (by norm_num) x) = x := by
  rw [← RingHom.comp_apply, τ_comp (hab := by norm_num),
    τ_mod (a := 2 * 3) (b := 1) (by norm_num) (by norm_num) (by norm_num), τ_one]; rfl

lemma absNorm_of_inv (f g : 𝓞 K5 →+* 𝓞 K5) (h1 : ∀ x, f (g x) = x) (h2 : ∀ x, g (f x) = x)
    (x : 𝓞 K5) : Ideal.absNorm (Ideal.span {f x}) = Ideal.absNorm (Ideal.span {x}) :=
  absNorm_equiv (RingEquiv.ofRingHom f g (RingHom.ext h1) (RingHom.ext h2)) x

lemma phi_sub_three : φ - 3 = ζ ^ 4 * lam ^ 2 := by linear_combination (2 - ζ) * ζ_pow_five

lemma lam_dvd_τ3_lam : lam ∣ τ 3 (by norm_num) lam := by
  refine ⟨1 + ζ + ζ ^ 2, ?_⟩
  simp only [lam, map_sub, map_one, τ_ζ]; ring

lemma zeta_pow_primary {a : ℕ} {m : ℤ} (h : lam ^ 2 ∣ ζ ^ a * m + 1) : ζ ^ a = 1 := by
  have h1 : lam ∣ (m : 𝓞 K5) + 1 := by
    have hz : lam ∣ ζ ^ a - 1 := by
      have := sub_dvd_pow_sub_pow ζ 1 a; rw [one_pow] at this
      exact dvd_trans ⟨-1, by ring⟩ this
    have := dvd_sub (dvd_trans (dvd_pow_self lam (by norm_num)) h) (dvd_mul_of_dvd_left hz (m : 𝓞 K5))
    convert this using 1; ring
  have h5 : (5 : ℤ) ∣ m + 1 := lam_dvd_int (by exact_mod_cast h1)
  have h2 : lam ^ 2 ∣ (m : 𝓞 K5) * (ζ ^ a - 1) := by
    have := dvd_sub h (lam_pow_dvd_of_five_dvd h5 (j := 2) (by norm_num))
    push_cast at this; convert this using 1; ring
  have hm : ¬ lam ∣ (m : 𝓞 K5) := by
    intro hl; have := lam_dvd_int hl; omega
  have hcop : IsCoprime (lam ^ 2) (m : 𝓞 K5) :=
    ((Prime.coprime_iff_not_dvd lam_prime).mpr hm).pow_left
  have h3 := hcop.dvd_of_dvd_mul_left h2
  rw [ζ_pow_mod a] at h3 ⊢
  have ha : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos (a % 5) with h0 | hpos
  · rw [h0, pow_zero]
  · exfalso
    obtain ⟨w, hw, hw'⟩ := one_sub_pow_eq (a % 5) (by omega)
    have : lam ^ 2 ∣ lam * w := by
      have := dvd_neg.mpr h3; rw [neg_sub, hw'] at this; exact this
    have := lam_cancel (j := 1) (by simpa [pow_succ] using this)
    rw [pow_one] at this
    obtain ⟨U, rfl⟩ := hw
    exact not_lam_dvd_unit U this

lemma real_congr {r : 𝓞 K5} (hr : σ r = r) : ∃ n : ℤ, lam ^ 2 ∣ r - n := by
  obtain ⟨a, c, rfl⟩ := real_form hr
  exact ⟨a + 3 * c, ⟨c * ζ ^ 4, by push_cast; linear_combination (c : 𝓞 K5) * phi_sub_three⟩⟩

lemma congr_mul {I : 𝓞 K5} {x x' y y' : 𝓞 K5} (hx : I ∣ x - x') (hy : I ∣ y - y') :
    I ∣ x * y - x' * y' := by
  have : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_left hx _) (dvd_mul_of_dvd_right hy _)

include hd in
/-- **Eisenstein reciprocity for `2`** (degree-one primes, `l = 5`): if `2` is a fifth power
modulo `P = ker ψ` and `π` is a primary generator of `P`, then `π³ ≡ 1 (mod 2)`. -/
theorem eis2 {π : 𝓞 K5} (hker : ∀ x, ψ x = 0 ↔ π ∣ x) {c : ℤ} (hπc : lam ^ 2 ∣ π - c)
    (h2 : (2 : ZMod p) ^ kk p = 1) : (2 : 𝓞 K5) ∣ π ^ 3 - 1 := by
  have hspan : Ideal.span {π} = RingHom.ker ψ := by
    ext x; rw [Ideal.mem_span_singleton, RingHom.mem_ker, hker]
  have hpO : (p : 𝓞 K5) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hπ0 : π ≠ 0 := by
    intro h
    have := (hker (p : 𝓞 K5)).mp (by simp)
    rw [h, zero_dvd_iff] at this; exact hpO this
  have hπp : Prime π := (Ideal.span_singleton_prime hπ0).mp (hspan ▸ RingHom.ker_isPrime ψ)
  have hJ1 : π ∣ JJ ψ hd := (hker _).mp (ψ_JJ ψ hd)
  have hJ2 : τ 3 (by norm_num) π ∣ JJ ψ hd := by
    obtain ⟨t, ht⟩ := (hker _).mp (ψ_τ2_JJ ψ hd)
    exact ⟨τ 3 (by norm_num) t, by rw [← τ32 (JJ ψ hd), ht, map_mul]⟩
  have hnd : ¬ π ∣ τ 3 (by norm_num) π := by
    intro h
    set n : ℤ := ((ψ ζ).val : ℤ)
    have hn : ψ (n : 𝓞 K5) = ψ ζ := by
      rw [map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]
    have h1 : π ∣ ζ - n := (hker _).mp (by rw [map_sub, hn, sub_self])
    have h2' : τ 3 (by norm_num) π ∣ ζ ^ 3 - n := by
      obtain ⟨t, ht⟩ := h1
      exact ⟨τ 3 (by norm_num) t, by
        rw [← τ_ζ (c := 3) (by norm_num), ← map_intCast (τ 3 (by norm_num)) n, ← map_sub, ht,
          map_mul]⟩
    have h3 : ψ (ζ ^ 3 - n) = 0 := (hker _).mpr (dvd_trans h h2')
    rw [map_sub, hn, map_pow] at h3
    have e3 : ζ ^ 3 = ζ ^ 1 := ζ_inj ψ hd (by rw [pow_one]; linear_combination h3)
    have hz : ζ ≠ 0 := fun h0 => by simpa [h0] using ζ_pow_five
    have : ζ ^ 2 = 1 := mul_left_cancel₀ hz (by linear_combination e3)
    exact ζ_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) this
  have hcop : IsCoprime π (τ 3 (by norm_num) π) := (Prime.coprime_iff_not_dvd hπp).mpr hnd
  obtain ⟨w, hw⟩ := hcop.mul_dvd hJ1 hJ2
  -- `w` is a unit
  have hcard : Ideal.absNorm (Ideal.span {π}) = p := by
    rw [hspan, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hs : Function.Surjective ψ := fun y => ⟨(y.val : 𝓞 K5), by rw [map_natCast, ZMod.natCast_zmod_val]⟩
    rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, Nat.card_zmod]
  have hcard3 : Ideal.absNorm (Ideal.span {τ 3 (by norm_num) π}) = p := by
    rw [← hcard]; exact absNorm_of_inv _ _ τ32 τ23 π
  have hJσ := JJ_mul_σ ψ hd
  have hA : Ideal.absNorm (Ideal.span {JJ ψ hd}) ^ 2 = (p ^ 2) ^ 2 := by
    have : Ideal.absNorm (Ideal.span {JJ ψ hd * σ (JJ ψ hd)}) = Ideal.absNorm (Ideal.span {(p : 𝓞 K5)}) := by
      rw [hJσ]
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Ideal.absNorm_span_natCast,
      finrank_O] at this
    have hs : Ideal.absNorm (Ideal.span {σ (JJ ψ hd)}) = Ideal.absNorm (Ideal.span {JJ ψ hd}) :=
      absNorm_equiv σ.toRingEquiv (JJ ψ hd)
    rw [hs] at this; rw [sq, this]; ring
  have hA' : Ideal.absNorm (Ideal.span {JJ ψ hd}) = p ^ 2 := Nat.pow_left_injective two_ne_zero hA
  rw [hw, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    map_mul, map_mul, hcard, hcard3] at hA'
  have hw1 : Ideal.absNorm (Ideal.span {w}) = 1 := by
    have hp0 : 0 < p * p := Nat.mul_pos hp.out.pos hp.out.pos
    have : p * p * Ideal.absNorm (Ideal.span {w}) = p * p * 1 := by rw [hA']; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  have hwu : IsUnit w := Ideal.span_singleton_eq_top.mp (Ideal.absNorm_eq_one_iff.mp hw1)
  -- `w` is real
  obtain ⟨a, r, hr, hrσ⟩ := unit_decomp hwu.unit
  rw [IsUnit.unit_spec] at hr
  obtain ⟨n, hn⟩ := real_congr hrσ
  have hτc : lam ^ 2 ∣ τ 3 (by norm_num) π - c := by
    obtain ⟨t, ht⟩ := hπc
    obtain ⟨v, hv⟩ := lam_dvd_τ3_lam
    exact ⟨v ^ 2 * τ 3 (by norm_num) t, by
      rw [← map_intCast (τ 3 (by norm_num)) c, ← map_sub, ht, map_mul, map_pow, hv]; ring⟩
  have hprim := JJ_primary ψ hd
  have hz1 : ζ ^ a = 1 := by
    apply zeta_pow_primary (m := c * c * n)
    have hc2 := congr_mul (congr_mul hπc hτc) hn
    have := dvd_sub hprim (dvd_mul_of_dvd_right hc2 (ζ ^ a))
    rw [hw, hr] at this; push_cast; convert this using 1; ring
  rw [hz1, one_mul] at hr
  -- mod 2 in the residue field `F₁₆`
  haveI hmax : (Ideal.span {(2 : 𝓞 K5)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime two_prime.ne_zero).mpr two_prime)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact two_prime.ne_zero)
  letI : Field (𝓞 K5 ⧸ Ideal.span {(2 : 𝓞 K5)}) := Ideal.Quotient.field _
  set mk := Ideal.Quotient.mk (Ideal.span {(2 : 𝓞 K5)})
  have key : ∀ x y : 𝓞 K5, (2 : 𝓞 K5) ∣ x - y ↔ mk x = mk y := by
    intro x y; rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hχ2 : χ5 ψ hd 2 = 1 := by
    rcases χ5_cases ψ hd 2 with h0 | ⟨i, hi⟩
    · exfalso; have := ψ_χ5 ψ hd 2; rw [h0, map_zero, h2] at this; exact zero_ne_one this
    · rw [hi]
      have : ζ ^ i = ζ ^ 0 := ζ_inj ψ hd (by rw [← map_pow, ← hi, ψ_χ5, h2, pow_zero])
      rw [this, pow_zero]
  have hJ1' : mk (JJ ψ hd) = 1 := by
    have := (key _ _).mp (χ5_two_inv_sq_mod2 ψ hd)
    rw [this, χ5_inv, hχ2, map_one, one_pow, map_one]
  have hr3 : mk r ^ 3 = 1 := by
    have h4 := (key _ _).mp (frob4 r); rw [hrσ, map_pow] at h4
    have hr0 : mk r ≠ 0 := by
      intro h0
      have : mk (JJ ψ hd) = 0 := by rw [hw, hr, map_mul, h0, mul_zero]
      rw [hJ1'] at this; exact one_ne_zero this
    have : mk r * (mk r ^ 3 - 1) = 0 := by linear_combination h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hr0)
  have hπ0' : mk π ≠ 0 := by
    intro h0
    have : mk (JJ ψ hd) = 0 := by rw [hw, map_mul, map_mul, h0, zero_mul, zero_mul]
    rw [hJ1'] at this; exact one_ne_zero this
  set Y := mk π ^ 3 with hY
  have hY5 : Y ^ 5 = 1 := by
    have h16 := (key _ _).mp (frob16 π); rw [map_pow] at h16
    have : mk π * (mk π ^ 15 - 1) = 0 := by linear_combination h16
    have := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hπ0')
    rw [hY, ← pow_mul]; exact this
  have hτY : mk (τ 3 (by norm_num) π) ^ 3 = Y ^ 8 := by
    have h8 := (key _ _).mp (frob8 (π ^ 3))
    rw [map_pow (τ 3 (by norm_num))] at h8
    rw [← map_pow, ← h8]; simp only [map_pow, hY]
  have hY9 : Y ^ 9 = 1 := by
    have : mk (JJ ψ hd) ^ 3 = 1 := by rw [hJ1', one_pow]
    rw [hw, hr, map_mul, map_mul, mul_pow, mul_pow, hτY, hr3, ← hY] at this
    linear_combination this
  have hY1 : Y = 1 := by
    have h4 : Y ^ 4 = 1 := by linear_combination hY9 - Y ^ 4 * hY5
    linear_combination hY5 - Y * h4
  exact (key _ _).mpr (by rw [map_pow, map_one]; exact hY1)

end Char

end OMA672Z5

-- ===== CaseA1.lean =====

open NumberField Polynomial

namespace OMA672Z5

section DegOne

lemma frob_mod_five {F : Type*} [Field F] {z : F} (hz : z ^ 5 = 1) (n : ℕ) : z ^ n = z ^ (n % 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, hz, one_pow, mul_one]

/-- In a field, a fifth root of unity `z ≠ 1` with `z^e = z` forces `e ≡ 1 (mod 5)`. -/
lemma root_exp {F : Type*} [Field F] {z : F} (hz : z ^ 5 = 1) (hz1 : z ≠ 1) {e : ℕ}
    (h : z ^ e = z) : e % 5 = 1 := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hord : orderOf z = 5 := orderOf_eq_prime hz hz1
  have hpr : IsPrimitiveRoot z 5 := by rw [← hord]; exact IsPrimitiveRoot.orderOf z
  rcases Nat.eq_zero_or_pos e with h0 | hpos
  · subst h0; exact absurd (h.symm.trans (pow_zero z)) hz1
  · have : z ^ (e - 1) = 1 := by
      apply mul_left_cancel₀ hz0
      rw [← pow_succ', Nat.sub_add_cancel hpos, h, mul_one]
    have := (hpr.pow_eq_one_iff_dvd _).mp this
    omega

/-- Field-level core of the degree-one lemma. -/
theorem deg_one_field {F : Type*} [Field F] [Finite F] (mk : 𝓞 K5 →+* F) (hz1 : mk ζ ≠ 1)
    {X Y : 𝓞 K5} (hX : σ X = X) (hY : σ Y = Y) (hY0 : mk Y ≠ 0) (hdiv : mk (X + ζ * Y) = 0) :
    ∃ n : ℤ, mk ζ = n := by
  set p := ringChar F
  haveI : CharP F p := ringChar.charP F
  haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite F p⟩
  haveI hpf : Fact p.Prime := CharP.char_is_prime_of_pos F p
  set z := mk ζ
  set f := mk φ
  have hz5 : z ^ 5 = 1 := by rw [← map_pow, ζ_pow_five, map_one]
  have hf : f = 1 + z + z ^ 4 := by simp [f, z]
  obtain ⟨a, b, hXab⟩ := real_form hX
  obtain ⟨a', b', hYab⟩ := real_form hY
  have hXf : mk X = a + b * f := by rw [hXab, map_add, map_mul, map_intCast, map_intCast]
  have hYf : mk Y = a' + b' * f := by rw [hYab, map_add, map_mul, map_intCast, map_intCast]
  have hB : (a' : F) + b' * f ≠ 0 := by rw [← hYf]; exact hY0
  have hzA : z * ((a' : F) + b' * f) = -((a : F) + b * f) := by
    have := hdiv
    rw [map_add, map_mul, hXf, hYf] at this
    linear_combination this
  have himg : ∀ h : F →+* F, h z * ((a' : F) + b' * h f) = -((a : F) + b * h f) := by
    intro h; have := congrArg h hzA
    simp only [map_mul, map_add, map_neg, map_intCast] at this; exact this
  set Fr := frobenius F p
  have hfsq : f ^ 2 = f + 1 := by rw [← map_pow, φ_sq, map_add, map_one]
  have hFr : Fr f = f ∨ Fr f = 1 - f := by
    have h1 : (Fr f) ^ 2 = Fr f + 1 := by rw [← map_pow, hfsq, map_add, map_one]
    have : (Fr f - f) * (Fr f - (1 - f)) = 0 := by linear_combination h1 - hfsq
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hFr2 : Fr (Fr f) = f := by
    rcases hFr with h | h
    · rw [h, h]
    · rw [h, map_sub, map_one, h]; ring
  have huniq : ∀ w : F, w * ((a' : F) + b' * f) = -((a : F) + b * f) → w = z := by
    intro w hw
    exact mul_right_cancel₀ hB (by rw [hw, hzA])
  have hFrz : Fr z = z ^ (p % 5) := by
    rw [frobenius_def]; exact frob_mod_five hz5 p
  have hFr2z : Fr (Fr z) = z := by
    apply huniq
    have := himg (Fr.comp Fr); simp only [RingHom.comp_apply, hFr2] at this; exact this
  have he : (p % 5 * (p % 5)) % 5 = 1 := by
    apply root_exp hz5 hz1
    rw [hFrz, map_pow, hFrz, ← pow_mul] at hFr2z; exact hFr2z
  have hFrf : Fr f = f := by
    have hp5 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hcases : p % 5 = 1 ∨ p % 5 = 4 := by
      generalize p % 5 = e at he hp5 ⊢
      interval_cases e <;> omega
    have : Fr f = 1 + Fr z + Fr z ^ 4 := by rw [hf, map_add, map_add, map_one, map_pow]
    rw [this, hFrz, hf]
    rcases hcases with h | h <;> rw [h]
    · ring
    · rw [← pow_mul, frob_mod_five hz5 (4 * 4)]; ring
  have hFz : z ^ p = z := by
    have := huniq (Fr z) (by have := himg Fr; rwa [hFrf] at this)
    rwa [frobenius_def] at this
  have hbot : z ∈ (⊥ : Subfield F) := (Subfield.mem_bot_iff_pow_eq_self F p).mpr hFz
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p F).mp hbot
  exact ⟨n, hn.symm⟩

/-- Primes dividing `X + ζ Y` with `X, Y` real have residue degree one. -/
theorem deg_one {q : 𝓞 K5} (hq : Prime q) (hql : ¬ q ∣ lam) {X Y : 𝓞 K5} (hX : σ X = X)
    (hY : σ Y = Y) (hqY : ¬ q ∣ Y) (hdiv : q ∣ X + ζ * Y) : ∃ n : ℤ, q ∣ ζ - n := by
  have hq0 : q ≠ 0 := hq.ne_zero
  haveI hmax : (Ideal.span {q}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hq0).mpr hq)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0)
  letI : Field (𝓞 K5 ⧸ Ideal.span {q}) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K5 ⧸ Ideal.span {q}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0)
  have key : ∀ x : 𝓞 K5, Ideal.Quotient.mk (Ideal.span {q}) x = 0 ↔ q ∣ x := by
    intro x; rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hz1 : Ideal.Quotient.mk (Ideal.span {q}) ζ ≠ 1 := by
    intro h; apply hql
    rw [← key, map_sub, map_one]; exact sub_eq_zero.mpr h.symm
  obtain ⟨n, hn⟩ := deg_one_field (F := 𝓞 K5 ⧸ Ideal.span {q}) (Ideal.Quotient.mk _) hz1 hX hY
    (fun h => hqY ((key _).mp h)) ((key _).mpr hdiv)
  exact ⟨n, (key _).mp (by rw [map_sub, hn, map_intCast, sub_self])⟩

end DegOne

section Psi

lemma exists_psi_field {F : Type*} [Field F] [Finite F] (mk : 𝓞 K5 →+* F)
    (hsurj : Function.Surjective mk) {n : ℤ} (hn : mk ζ = n) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, Nonempty (F ≃+* ZMod p) := by
  set p := ringChar F
  haveI : CharP F p := ringChar.charP F
  haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite F p⟩
  haveI hpf : Fact p.Prime := CharP.char_is_prime_of_pos F p
  set c := ZMod.castHom (dvd_refl p) F
  have hinj : Function.Injective c := c.injective
  have hs : Function.Surjective c := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨a, b, d, e, rfl⟩ := exists_coord x
    refine ⟨((a + b * n + d * n ^ 2 + e * n ^ 3 : ℤ) : ZMod p), ?_⟩
    simp only [map_intCast, map_add, map_mul, map_pow, hn]; push_cast; ring
  exact ⟨p, hpf, ⟨(RingEquiv.ofBijective c ⟨hinj, hs⟩).symm⟩⟩

/-- A degree-one prime gives a reduction map to `ZMod p`. -/
theorem exists_psi {q : 𝓞 K5} (hq : Prime q) (hql : ¬ q ∣ lam) {n : ℤ} (hn : q ∣ ζ - n) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ ψ : 𝓞 K5 →+* ZMod p, ψ ζ ≠ 1 ∧ ∀ x, ψ x = 0 ↔ q ∣ x := by
  have hq0 : q ≠ 0 := hq.ne_zero
  haveI hmax : (Ideal.span {q}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hq0).mpr hq)
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0)
  letI : Field (𝓞 K5 ⧸ Ideal.span {q}) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K5 ⧸ Ideal.span {q}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0)
  have key : ∀ x : 𝓞 K5, Ideal.Quotient.mk (Ideal.span {q}) x = 0 ↔ q ∣ x := by
    intro x; rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hmn : Ideal.Quotient.mk (Ideal.span {q}) ζ = n := by
    have := (key _).mpr hn; rw [map_sub, map_intCast] at this; exact sub_eq_zero.mp this
  obtain ⟨p, hp, ⟨e⟩⟩ := exists_psi_field (F := 𝓞 K5 ⧸ Ideal.span {q}) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective hmn
  refine ⟨p, hp, e.toRingHom.comp (Ideal.Quotient.mk _), ?_, ?_⟩
  · intro h
    apply hql
    have : Ideal.Quotient.mk (Ideal.span {q}) ζ = 1 := by
      have := congrArg e.symm h; simpa using this
    rw [← key, map_sub, map_one, this, sub_self]
  · intro x
    rw [RingHom.comp_apply, ← key]
    constructor
    · intro h; have := congrArg e.symm h; simpa using this
    · intro h; simp [h]

end Psi

section Symbol

lemma σ_φ : σ φ = φ := by
  simp only [φ, map_add, map_one, map_pow, σ_ζ]
  have h16 : (ζ ^ 4) ^ 4 = ζ := by rw [← pow_mul, ζ_pow_mod]; norm_num
  rw [h16]; ring

lemma unitsMap_σ_Φ : Units.map (σ : 𝓞 K5 →* 𝓞 K5) Φ = Φ := Units.ext (by simp [σ_φ])

/-- Real units are `±φ^m`. -/
lemma real_unit (u : (𝓞 K5)ˣ) (hu : σ (u : 𝓞 K5) = u) :
    ∃ m : ℤ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (u : 𝓞 K5) = s * ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) := by
  obtain ⟨k, m, s, hs, hu'⟩ := unit_form u
  refine ⟨m, s, hs, ?_⟩
  have hσΦ : σ ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) = ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) := by
    have := congrArg (fun v : (𝓞 K5)ˣ => (v : 𝓞 K5)) (congrArg (· ^ m) unitsMap_σ_Φ)
    simp only [← map_zpow] at this; exact this
  rw [hu', map_mul, map_mul, map_pow, σ_ζ, hσΦ, map_intCast] at hu
  have hΦ0 : ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) ≠ 0 := Units.ne_zero _
  have hs0 : (s : 𝓞 K5) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have e1 : (ζ ^ 4) ^ k = ζ ^ k := by
    have := mul_right_cancel₀ hΦ0 hu
    exact mul_left_cancel₀ hs0 this
  have e2 : ζ ^ (3 * k) = 1 := by
    have hz : ζ ^ k ≠ 0 := pow_ne_zero _ (fun h0 => by simpa [h0] using ζ_pow_five)
    apply mul_left_cancel₀ hz
    rw [← pow_add, mul_one, show k + 3 * k = 4 * k by ring, pow_mul]; exact e1
  have h5 : 5 ∣ 3 * k := (ζ_prim.pow_eq_one_iff_dvd _).mp e2
  have : ζ ^ k = 1 := (ζ_prim.pow_eq_one_iff_dvd _).mpr (by omega)
  rw [hu', this, mul_one]

variable {p : ℕ} [hp : Fact p.Prime] (ψ : 𝓞 K5 →+* ZMod p) (hd : ψ ζ ≠ 1)

include hd in
lemma kk_even : Even (kk p) := by
  have h5 := five_kk ψ hd
  have hp2 := p_ne_two ψ hd
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have : Even (p - 1) := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rw [← h5] at this
  exact (Nat.even_mul.mp this).resolve_left (by decide)

include hd in
lemma ψ_pow_kk_five {t : 𝓞 K5} (ht : ψ t ≠ 0) : (ψ t ^ 5) ^ kk p = 1 := by
  rw [← pow_mul, five_kk ψ hd]; exact ZMod.pow_card_sub_one_eq_one ht

include hd in
lemma ψ_real_unit (hφ : ψ φ ^ kk p = 1) (u : (𝓞 K5)ˣ) (hu : σ (u : 𝓞 K5) = u) :
    ψ u ^ kk p = 1 := by
  obtain ⟨m, s, hs, hu'⟩ := real_unit u hu
  have he := kk_even ψ hd
  have hU : (Units.map (ψ : 𝓞 K5 →* ZMod p) Φ) ^ kk p = 1 := Units.ext (by simpa using hφ)
  have hΦm : ψ ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) ^ kk p = 1 := by
    have : ψ ((Φ ^ m : (𝓞 K5)ˣ) : 𝓞 K5) = ((Units.map (ψ : 𝓞 K5 →* ZMod p) Φ) ^ m : (ZMod p)ˣ) := by
      rw [← map_zpow]; rfl
    rw [this, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hU, one_zpow, Units.val_one]
  rw [hu', map_mul, mul_pow, hΦm, mul_one, map_intCast]
  rcases hs with rfl | rfl
  · simp
  · simp [he.neg_one_pow]

include hd in
/-- **The residue symbol computation**: `2` is a fifth power modulo every prime dividing `X + ζY`. -/
theorem two_fifth_power {X Y t2 W : 𝓞 K5} {r2 r0 : (𝓞 K5)ˣ} (hr2 : σ (r2 : 𝓞 K5) = r2)
    (hr0 : σ (r0 : 𝓞 K5) = r0) {j : ℕ} (hj : j = 1 ∨ j = 3)
    (h1 : ψ (X + ζ * Y) = 0) (hY : ψ Y ≠ 0) (ht2 : ψ t2 ≠ 0) (hσt2 : ψ (σ t2) ≠ 0)
    (hW : ψ W ≠ 0) (h2 : X + ζ ^ 2 * Y = ζ * r2 * t2 ^ 5)
    (h3 : X + ζ ^ 3 * Y = ζ ^ 4 * r2 * (σ t2) ^ 5) (h0 : X + Y = 2 ^ j * r0 * W ^ 5) :
    (2 : ZMod p) ^ kk p = 1 := by
  set d := ψ ζ
  set y := ψ Y
  set k := kk p
  have he := kk_even ψ hd
  have hd0 : d ≠ 0 := (d_prim ψ hd).ne_zero (by norm_num)
  have hd5 : d ^ 5 = 1 := (d_prim ψ hd).pow_eq_one
  have hdk : (d ^ 5) ^ k = 1 := by rw [hd5, one_pow]
  have hX : ψ X = -(d * y) := by
    rw [map_add, map_mul] at h1; linear_combination h1
  have e2 := congrArg ψ h2
  have e3 := congrArg ψ h3
  have e0 := congrArg ψ h0
  simp only [map_add, map_mul, map_pow, hX] at e2 e3 e0
  rw [show ψ (r2 : 𝓞 K5) = ψ r2 from rfl] at e2
  -- k-th powers
  have k2 : (d * ψ r2) ^ k = (y * (d ^ 2 - d)) ^ k := by
    have := congrArg (· ^ k) e2
    rw [mul_pow, mul_pow, ψ_pow_kk_five ψ hd ht2, mul_one] at this
    rw [mul_pow]; linear_combination -this
  have k3 : (d ^ 4 * ψ r2) ^ k = (y * (d ^ 3 - d)) ^ k := by
    have := congrArg (· ^ k) e3
    rw [mul_pow, mul_pow, ψ_pow_kk_five ψ hd hσt2, mul_one] at this
    rw [mul_pow]; linear_combination -this
  have hcyc : 1 + d + d ^ 2 + d ^ 3 + d ^ 4 = 0 := by
    have := congrArg ψ cyc; simpa using this
  have hd1 : d - 1 ≠ 0 := sub_ne_zero.mpr hd
  have hy0 : y ≠ 0 := hY
  have hR0 : ψ r2 ^ k ≠ 0 := pow_ne_zero _ (fun h => by
    have := (r2.isUnit.map ψ); rw [h] at this; exact not_isUnit_zero this)
  -- (d+1)^k = d^(3k)
  have hA : (d ^ k * ψ r2 ^ k) * (d + 1) ^ k = (d ^ k * ψ r2 ^ k) * d ^ (3 * k) := by
    have e2' : (d * ψ r2) ^ k = y ^ k * d ^ k * (d - 1) ^ k := by
      rw [k2, show d ^ 2 - d = d * (d - 1) by ring, mul_pow, mul_pow]; ring
    have e3' : (d ^ 4 * ψ r2) ^ k = y ^ k * d ^ k * (d - 1) ^ k * (d + 1) ^ k := by
      rw [k3, show d ^ 3 - d = d * (d - 1) * (d + 1) by ring, mul_pow, mul_pow, mul_pow]; ring
    rw [mul_pow] at e2' e3'
    have : (d ^ 4) ^ k = d ^ k * d ^ (3 * k) := by rw [← pow_mul, ← pow_add]; ring_nf
    rw [this] at e3'
    linear_combination (d + 1) ^ k * e2' - e3'
  have hB : (d + 1) ^ k = d ^ (3 * k) :=
    mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hd0) hR0) hA
  have hφ : ψ φ ^ k = 1 := by
    have hrel : d + 1 = -(d ^ 3 * ψ φ) := by
      simp only [φ, map_add, map_one, map_pow]
      linear_combination hcyc + d ^ 2 * hd5
    rw [hrel, neg_pow, he.neg_one_pow, one_mul, mul_pow, ← pow_mul, mul_comm 3 k] at hB
    have : d ^ (k * 3) * ψ φ ^ k = d ^ (k * 3) * 1 := by rw [hB]; ring
    exact mul_left_cancel₀ (pow_ne_zero _ hd0) this
  have hr2k : ψ r2 ^ k = 1 := ψ_real_unit ψ hd hφ r2 hr2
  have hr0k : ψ r0 ^ k = 1 := ψ_real_unit ψ hd hφ r0 hr0
  have hYk : y ^ k * (d - 1) ^ k = 1 := by
    have e2' : (d * ψ r2) ^ k = y ^ k * d ^ k * (d - 1) ^ k := by
      rw [k2, show d ^ 2 - d = d * (d - 1) by ring, mul_pow, mul_pow]; ring
    rw [mul_pow, hr2k, mul_one] at e2'
    have : d ^ k * (y ^ k * (d - 1) ^ k) = d ^ k * 1 := by linear_combination -e2'
    exact mul_left_cancel₀ (pow_ne_zero _ hd0) this
  have h2k : ((2 : ZMod p) ^ k) ^ j = 1 := by
    have := congrArg (· ^ k) e0
    have hW5 : (ψ W ^ 5) ^ k = 1 := ψ_pow_kk_five ψ hd hW
    rw [mul_pow, mul_pow, hW5, mul_one, hr0k, mul_one, ← pow_mul, mul_comm j k, pow_mul] at this
    have hl : (-(d * y) + y) ^ k = y ^ k * (d - 1) ^ k := by
      rw [show -(d * y) + y = -(y * (d - 1)) by ring, neg_pow, he.neg_one_pow, one_mul, mul_pow]
    rw [hl, hYk] at this
    simpa [map_ofNat] using this.symm
  have h25 : ((2 : ZMod p) ^ k) ^ 5 = 1 := by
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact p_ne_two ψ hd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
    rw [← pow_mul, mul_comm, five_kk ψ hd]; exact ZMod.pow_card_sub_one_eq_one h20
  rcases hj with rfl | rfl
  · simpa using h2k
  · linear_combination (((2 : ZMod p) ^ k) ^ 3 + 1) * h2k - ((2 : ZMod p) ^ k) * h25

end Symbol

end OMA672Z5


-- ===== CaseA2.lean =====

open NumberField

namespace OMA672Z5

section Good

lemma zeta_primary' {a : ℕ} {m c : ℤ} (h : lam ^ 2 ∣ ζ ^ a * m - c) (hm : ¬ (5 : ℤ) ∣ m) :
    ζ ^ a = 1 := by
  have hz : lam ∣ ζ ^ a - 1 := by
    have := sub_dvd_pow_sub_pow ζ 1 a; rw [one_pow] at this
    exact dvd_trans ⟨-1, by ring⟩ this
  have h1 : lam ∣ (m : 𝓞 K5) - c := by
    have := dvd_sub (dvd_trans (dvd_pow_self lam (by norm_num)) h) (dvd_mul_of_dvd_left hz (m : 𝓞 K5))
    convert this using 1; ring
  have h5 : (5 : ℤ) ∣ m - c := lam_dvd_int (by push_cast; exact h1)
  have h2 : lam ^ 2 ∣ (m : 𝓞 K5) * (ζ ^ a - 1) := by
    have := dvd_sub h (lam_pow_dvd_of_five_dvd h5 (j := 2) (by norm_num))
    push_cast at this; convert this using 1; ring
  have hml : ¬ lam ∣ (m : 𝓞 K5) := fun hl => hm (lam_dvd_int hl)
  have hcop : IsCoprime (lam ^ 2) (m : 𝓞 K5) :=
    ((Prime.coprime_iff_not_dvd lam_prime).mpr hml).pow_left
  have h3 := hcop.dvd_of_dvd_mul_left h2
  rw [ζ_pow_mod a] at h3 ⊢
  rcases Nat.eq_zero_or_pos (a % 5) with h0 | hpos
  · rw [h0, pow_zero]
  · exfalso
    have ha : a % 5 < 5 := Nat.mod_lt _ (by norm_num)
    obtain ⟨w, hw, hw'⟩ := one_sub_pow_eq (a % 5) (by omega)
    have : lam ^ 2 ∣ lam * w := by
      have := dvd_neg.mpr h3; rw [neg_sub, hw'] at this; exact this
    have := lam_cancel (j := 1) (by simpa [pow_succ] using this)
    rw [pow_one] at this
    obtain ⟨U, rfl⟩ := hw
    exact not_lam_dvd_unit U this

lemma real_unit_cube {r : 𝓞 K5} (hr : σ r = r) (hu : IsUnit r) : (2 : 𝓞 K5) ∣ r ^ 3 - 1 := by
  have h := frob4 r
  rw [hr, show r ^ 4 - r = r * (r ^ 3 - 1) by ring] at h
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hcop : IsCoprime (2 : 𝓞 K5) r := ⟨0, v, by rw [zero_mul, zero_add, mul_comm]; exact hv⟩
  exact hcop.dvd_of_dvd_mul_left h

/-- `x` is *good* if its primary normalisation is a cube root of unity mod 2. -/
def Good (x : 𝓞 K5) : Prop :=
  ∀ (k : ℕ) (c : ℤ), lam ^ 2 ∣ ζ ^ k * x - c → (2 : 𝓞 K5) ∣ (ζ ^ k * x) ^ 3 - 1

lemma int_not_five {x : 𝓞 K5} (hx : ¬ lam ∣ x) {k : ℕ} {c : ℤ} (h : lam ^ 2 ∣ ζ ^ k * x - c) :
    ¬ (5 : ℤ) ∣ c := by
  intro h5
  apply hx
  have hu : IsUnit (ζ ^ k) := (ζ_prim.isUnit (by norm_num)).pow k
  have h1 : lam ∣ ζ ^ k * x := by
    have h5' : lam ∣ (c : 𝓞 K5) := by
      simpa using lam_pow_dvd_of_five_dvd h5 (j := 1) (by norm_num)
    have := dvd_add (dvd_trans (dvd_pow_self lam two_ne_zero) h) h5'
    convert this using 1; ring
  obtain ⟨U, hU⟩ := hu
  rw [← hU] at h1
  exact (Units.dvd_mul_left).mp h1

lemma good_unit (u : (𝓞 K5)ˣ) : Good u := by
  intro k c h
  obtain ⟨a, r, hr, hrσ⟩ := unit_decomp u
  have hru : IsUnit r := by
    have : IsUnit (ζ ^ a * r) := hr ▸ u.isUnit
    exact isUnit_of_mul_isUnit_right this
  obtain ⟨n, hn⟩ := real_congr hrσ
  have hn5 : ¬ (5 : ℤ) ∣ n := by
    intro h5; obtain ⟨U, hU⟩ := hru
    apply not_lam_dvd_unit U; rw [hU]
    have := dvd_add hn (lam_pow_dvd_of_five_dvd h5 (j := 2) (by norm_num))
    exact dvd_trans (dvd_pow_self lam two_ne_zero) (by convert this using 1; ring)
  have h1 : lam ^ 2 ∣ ζ ^ (k + a) * n - c := by
    have := dvd_sub h (dvd_mul_of_dvd_right hn (ζ ^ (k + a)))
    rw [hr] at this; convert this using 1; ring
  have hz := zeta_primary' h1 hn5
  have : ζ ^ k * (u : 𝓞 K5) = r := by rw [hr, ← mul_assoc, ← pow_add, hz, one_mul]
  rw [this]; exact real_unit_cube hrσ hru

lemma cube_mul {x y : 𝓞 K5} (hx : (2 : 𝓞 K5) ∣ x ^ 3 - 1) (hy : (2 : 𝓞 K5) ∣ y ^ 3 - 1) :
    (2 : 𝓞 K5) ∣ (x * y) ^ 3 - 1 := by
  have : (x * y) ^ 3 - 1 = (x ^ 3 - 1) * y ^ 3 + (y ^ 3 - 1) := by ring
  rw [this]; exact dvd_add (dvd_mul_of_dvd_left hx _) hy

lemma good_mul {q a : 𝓞 K5} (hq : ¬ lam ∣ q) (ha : ¬ lam ∣ a) (hgq : Good q) (hga : Good a) :
    Good (q * a) := by
  intro k c h
  obtain ⟨k1, c1, h1⟩ := normalize hq
  obtain ⟨k2, c2, h2⟩ := normalize ha
  have h12 : lam ^ 2 ∣ (ζ ^ k1 * q) * (ζ ^ k2 * a) - c1 * c2 := by
    have := congr_mul h1 h2; push_cast; exact this
  set e := k + 4 * (k1 + k2)
  have hke : ζ ^ k = ζ ^ e * ζ ^ (k1 + k2) := by
    rw [← pow_add]; apply ζ_pow_eq_of_mod; omega
  have hc12 : ¬ (5 : ℤ) ∣ c1 * c2 := by
    have := int_not_five hq h1; have := int_not_five ha h2
    intro h5
    rcases (Int.prime_iff_natAbs_prime.mpr (by norm_num) : Prime (5 : ℤ)).dvd_or_dvd h5 with h | h
    <;> contradiction
  have he : ζ ^ e = 1 := by
    apply zeta_primary' (m := c1 * c2) (c := c) _ hc12
    have := dvd_sub h (dvd_mul_of_dvd_right h12 (ζ ^ e))
    rw [hke] at this; push_cast; convert this using 1; ring
  have : ζ ^ k * (q * a) = (ζ ^ k1 * q) * (ζ ^ k2 * a) := by
    rw [hke, he, one_mul, pow_add]; ring
  rw [this]
  exact cube_mul (hgq k1 c1 h1) (hga k2 c2 h2)

/-- If every prime factor of `t` is good (and `λ ∤ t`), then every divisor of `t` is good. -/
lemma good_of_dvd {t : 𝓞 K5} (ht : ¬ lam ∣ t) (hp : ∀ q, Prime q → q ∣ t → Good q) :
    ∀ x, x ∣ t → Good x := by
  intro x
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro h; exfalso; apply ht; rw [zero_dvd_iff.mp h]; exact dvd_zero _
  | h₂ x hx => intro _; obtain ⟨U, rfl⟩ := hx; exact good_unit U
  | h₃ a q ha0 hq ih =>
    intro h
    have hqt : q ∣ t := dvd_trans (dvd_mul_right q a) h
    have hat : a ∣ t := dvd_trans (dvd_mul_left a q) h
    exact good_mul (fun hl => ht (dvd_trans hl hqt)) (fun hl => ht (dvd_trans hl hat))
      (hp q hq hqt) (ih hat)

end Good

section KForce

lemma dvd25_coords {L0 L1 L2 L3 : ℤ}
    (h : (25 : 𝓞 K5) ∣ (L0 : 𝓞 K5) * ζ ^ 0 + (L1 : 𝓞 K5) * ζ ^ 1 + (L2 : 𝓞 K5) * ζ ^ 2
      + (L3 : 𝓞 K5) * ζ ^ 3) : 25 ∣ L0 ∧ 25 ∣ L1 ∧ 25 ∣ L2 ∧ 25 ∣ L3 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t0, t1, t2, t3, rfl⟩ := exists_coord t
  have := coord_eq (a := L0) (b := L1) (c := L2) (e := L3) (a' := 25 * t0) (b' := 25 * t1)
    (c' := 25 * t2) (e' := 25 * t3) (by push_cast; rw [pow_zero, pow_one, mul_one] at ht; rw [ht]; ring)
  obtain ⟨h0, h1, h2, h3⟩ := this
  exact ⟨⟨t0, h0⟩, ⟨t1, h1⟩, ⟨t2, h2⟩, ⟨t3, h3⟩⟩

lemma lam5_to_25 {D : 𝓞 K5} (h : lam ^ 5 ∣ D) : (25 : 𝓞 K5) ∣ D * lam ^ 3 * u5 ^ 2 := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨s, ?_⟩
  have : (25 : 𝓞 K5) = (lam ^ 4 * u5) ^ 2 := by rw [five_eq]; norm_num
  rw [this]; ring

lemma not_five_of_real {X : 𝓞 K5} {a b : ℤ} (hX : X = a + b * φ) (hl : ¬ lam ∣ X) :
    ¬ (5 : ℤ) ∣ a + 3 * b := by
  intro h5; apply hl
  have h1 := lam_pow_dvd_of_five_dvd h5 (j := 1) (by norm_num)
  rw [pow_one] at h1
  have h2 : lam ∣ φ - 3 := ⟨ζ ^ 4 * lam, by rw [phi_sub_three]; ring⟩
  rw [hX]
  have := dvd_add h1 (dvd_mul_of_dvd_right h2 (b : 𝓞 K5))
  convert this using 1; push_cast; ring

lemma kD1_0 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 0) * (X + ζ * Y) - ζ ^ 0 * (X + ζ ^ 4 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((5*c + 10*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((-10*c - 15*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((-10*c - 15*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (-5*(c:𝓞 K5) + (d:𝓞 K5)*ζ^19 + 2*(d:𝓞 K5)*ζ^18 + (d:𝓞 K5)*ζ^17 - 2*(d:𝓞 K5)*ζ^16 - 10*(d:𝓞 K5) + ζ^15*((c:𝓞 K5) - 5*(d:𝓞 K5)) + ζ^14*(2*(c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^13*((c:𝓞 K5) + (d:𝓞 K5)) + ζ^12*(-3*(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^11*(-8*(c:𝓞 K5) - (d:𝓞 K5)) + ζ^10*(-6*(c:𝓞 K5) - 4*(d:𝓞 K5)) + ζ^9*(3*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^8*(13*(c:𝓞 K5) + 13*(d:𝓞 K5)) + ζ^7*(13*(c:𝓞 K5) + 13*(d:𝓞 K5)) + ζ^6*(-(c:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^5*(-13*(c:𝓞 K5) - 20*(d:𝓞 K5)) + ζ^4*(-13*(c:𝓞 K5) - 17*(d:𝓞 K5)) + ζ^3*((c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^2*(12*(c:𝓞 K5) + 18*(d:𝓞 K5)) + ζ*(6*(c:𝓞 K5) + 11*(d:𝓞 K5))) * cyc

lemma kD2_0 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 0) * (X + ζ ^ 2 * Y) - ζ ^ 0 * (X + ζ ^ 3 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((5*c + 5*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((-5*c - 10*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((-5*c - 10*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (-5*(c:𝓞 K5) + (d:𝓞 K5)*ζ^18 + (d:𝓞 K5)*ζ^17 - (d:𝓞 K5)*ζ^16 - 2*(d:𝓞 K5)*ζ^15 - 5*(d:𝓞 K5) + ζ^14*((c:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^13*((c:𝓞 K5) + (d:𝓞 K5)) + ζ^12*(-(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^11*(-3*(c:𝓞 K5) - (d:𝓞 K5)) + ζ^10*(-4*(c:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^9*((c:𝓞 K5) - (d:𝓞 K5)) + ζ^8*(6*(c:𝓞 K5) + 6*(d:𝓞 K5)) + ζ^7*(6*(c:𝓞 K5) + 8*(d:𝓞 K5)) + ζ^6*((c:𝓞 K5) - (d:𝓞 K5)) + ζ^5*(-8*(c:𝓞 K5) - 9*(d:𝓞 K5)) + ζ^4*(-6*(c:𝓞 K5) - 10*(d:𝓞 K5)) + ζ^3*((c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^2*(6*(c:𝓞 K5) + 11*(d:𝓞 K5)) + ζ*(5*(c:𝓞 K5) + 5*(d:𝓞 K5))) * cyc

lemma kD1_1 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 1) * (X + ζ * Y) - ζ ^ 1 * (X + ζ ^ 4 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((-5*a - 10*b : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((10*a + 15*b : ℤ) : 𝓞 K5) * ζ ^ 2 + ((10*a + 15*b : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (5*(a:𝓞 K5) - (b:𝓞 K5)*ζ^19 - 2*(b:𝓞 K5)*ζ^18 - (b:𝓞 K5)*ζ^17 + 2*(b:𝓞 K5)*ζ^16 + 10*(b:𝓞 K5) + ζ^15*(-(a:𝓞 K5) + 5*(b:𝓞 K5)) + ζ^14*(-2*(a:𝓞 K5) + 3*(b:𝓞 K5)) + ζ^13*(-(a:𝓞 K5) - (b:𝓞 K5)) + ζ^12*(3*(a:𝓞 K5) - 2*(b:𝓞 K5)) + ζ^11*(8*(a:𝓞 K5) + (b:𝓞 K5)) + ζ^10*(6*(a:𝓞 K5) + 4*(b:𝓞 K5)) + ζ^9*(-3*(a:𝓞 K5) - 3*(b:𝓞 K5)) + ζ^8*(-13*(a:𝓞 K5) - 13*(b:𝓞 K5)) + ζ^7*(-13*(a:𝓞 K5) - 13*(b:𝓞 K5)) + ζ^6*((a:𝓞 K5) + 2*(b:𝓞 K5)) + ζ^5*(13*(a:𝓞 K5) + 20*(b:𝓞 K5)) + ζ^4*(13*(a:𝓞 K5) + 17*(b:𝓞 K5)) + ζ^3*(-(a:𝓞 K5) - 3*(b:𝓞 K5)) + ζ^2*(-12*(a:𝓞 K5) - 18*(b:𝓞 K5)) + ζ*(-6*(a:𝓞 K5) - 11*(b:𝓞 K5))) * cyc

lemma kD2_1 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 1) * (X + ζ ^ 2 * Y) - ζ ^ 1 * (X + ζ ^ 3 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((-5*a - 10*b + 5*c + 10*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((10*a + 15*b - 10*c - 15*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((10*a + 15*b - 10*c - 15*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (5*(a:𝓞 K5) - (b:𝓞 K5)*ζ^19 + 10*(b:𝓞 K5) - 5*(c:𝓞 K5) - (d:𝓞 K5)*ζ^21 - 2*(d:𝓞 K5)*ζ^20 - 10*(d:𝓞 K5) + ζ^18*(-2*(b:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^17*(-(b:𝓞 K5) - (c:𝓞 K5) + 4*(d:𝓞 K5)) + ζ^16*(2*(b:𝓞 K5) - 2*(c:𝓞 K5) + (d:𝓞 K5)) + ζ^15*(-(a:𝓞 K5) + 5*(b:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^14*(-2*(a:𝓞 K5) + 3*(b:𝓞 K5) + 4*(c:𝓞 K5) - (d:𝓞 K5)) + ζ^13*(-(a:𝓞 K5) - (b:𝓞 K5) + 7*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^12*(3*(a:𝓞 K5) - 2*(b:𝓞 K5) + 3*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^11*(8*(a:𝓞 K5) + (b:𝓞 K5) - 7*(c:𝓞 K5) - 5*(d:𝓞 K5)) + ζ^10*(6*(a:𝓞 K5) + 4*(b:𝓞 K5) - 12*(c:𝓞 K5) - 14*(d:𝓞 K5)) + ζ^9*(-3*(a:𝓞 K5) - 3*(b:𝓞 K5) - 7*(c:𝓞 K5) - 7*(d:𝓞 K5)) + ζ^8*(-13*(a:𝓞 K5) - 13*(b:𝓞 K5) + 7*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^7*(-13*(a:𝓞 K5) - 13*(b:𝓞 K5) + 14*(c:𝓞 K5) + 19*(d:𝓞 K5)) + ζ^6*((a:𝓞 K5) + 2*(b:𝓞 K5) + 5*(c:𝓞 K5) + 8*(d:𝓞 K5)) + ζ^5*(13*(a:𝓞 K5) + 20*(b:𝓞 K5) - 7*(c:𝓞 K5) - 13*(d:𝓞 K5)) + ζ^4*(13*(a:𝓞 K5) + 17*(b:𝓞 K5) - 11*(c:𝓞 K5) - 16*(d:𝓞 K5)) + ζ^3*(-(a:𝓞 K5) - 3*(b:𝓞 K5)) + ζ^2*(-12*(a:𝓞 K5) - 18*(b:𝓞 K5) + 10*(c:𝓞 K5) + 15*(d:𝓞 K5)) + ζ*(-6*(a:𝓞 K5) - 11*(b:𝓞 K5) + 5*(c:𝓞 K5) + 10*(d:𝓞 K5))) * cyc

lemma kD1_2 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 2) * (X + ζ * Y) - ζ ^ 2 * (X + ζ ^ 4 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((-5*a - 5*b - 5*c - 10*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((5*a + 10*b + 10*c + 15*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((5*a + 10*b + 10*c + 15*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (5*(a:𝓞 K5) + 5*(b:𝓞 K5) + 5*(c:𝓞 K5) - (d:𝓞 K5)*ζ^24 + 10*(d:𝓞 K5) + ζ^23*(-(b:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^22*(-2*(b:𝓞 K5) - (d:𝓞 K5)) + ζ^21*(-(b:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^20*((b:𝓞 K5) - (c:𝓞 K5) + 5*(d:𝓞 K5)) + ζ^19*(-(a:𝓞 K5) + 3*(b:𝓞 K5) - 2*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^18*(-2*(a:𝓞 K5) + 2*(b:𝓞 K5) - (c:𝓞 K5) - (d:𝓞 K5)) + ζ^17*(-(a:𝓞 K5) + (b:𝓞 K5) + 3*(c:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^16*(2*(a:𝓞 K5) + 3*(b:𝓞 K5) + 8*(c:𝓞 K5) + (d:𝓞 K5)) + ζ^15*(6*(a:𝓞 K5) + 4*(b:𝓞 K5) + 6*(c:𝓞 K5) + 4*(d:𝓞 K5)) + ζ^14*(5*(a:𝓞 K5) + 3*(b:𝓞 K5) - 3*(c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^13*(-5*(b:𝓞 K5) - 13*(c:𝓞 K5) - 13*(d:𝓞 K5)) + ζ^12*(-5*(a:𝓞 K5) - 12*(b:𝓞 K5) - 13*(c:𝓞 K5) - 13*(d:𝓞 K5)) + ζ^11*(-7*(a:𝓞 K5) - 9*(b:𝓞 K5) + (c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^10*(-2*(a:𝓞 K5) - (b:𝓞 K5) + 13*(c:𝓞 K5) + 20*(d:𝓞 K5)) + ζ^9*(7*(b:𝓞 K5) + 13*(c:𝓞 K5) + 17*(d:𝓞 K5)) + ζ^8*(4*(b:𝓞 K5) - (c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^7*(-(b:𝓞 K5) - 12*(c:𝓞 K5) - 18*(d:𝓞 K5)) + ζ^6*((a:𝓞 K5) + 2*(b:𝓞 K5) - 6*(c:𝓞 K5) - 11*(d:𝓞 K5)) + ζ^5*(7*(a:𝓞 K5) + 6*(b:𝓞 K5) + 5*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^4*(4*(a:𝓞 K5) + 7*(b:𝓞 K5) + 10*(c:𝓞 K5) + 15*(d:𝓞 K5)) + ζ^3*(-2*(a:𝓞 K5) - 3*(b:𝓞 K5)) + ζ^2*(-6*(a:𝓞 K5) - 11*(b:𝓞 K5) - 10*(c:𝓞 K5) - 15*(d:𝓞 K5)) + ζ*(-5*(a:𝓞 K5) - 5*(b:𝓞 K5) - 5*(c:𝓞 K5) - 10*(d:𝓞 K5))) * cyc

lemma kD2_2 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 2) * (X + ζ ^ 2 * Y) - ζ ^ 2 * (X + ζ ^ 3 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((-5*a - 5*b : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((5*a + 10*b : ℤ) : 𝓞 K5) * ζ ^ 2 + ((5*a + 10*b : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (5*(a:𝓞 K5) + 5*(b:𝓞 K5) - (d:𝓞 K5)*ζ^25 - 2*(d:𝓞 K5)*ζ^24 + ζ^23*(-(b:𝓞 K5) - (d:𝓞 K5)) + ζ^22*(-2*(b:𝓞 K5) + (d:𝓞 K5)) + ζ^21*(-(b:𝓞 K5) - (c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^20*((b:𝓞 K5) - 2*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^19*(-(a:𝓞 K5) + 3*(b:𝓞 K5) - (c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^18*(-2*(a:𝓞 K5) + 2*(b:𝓞 K5) + 2*(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^17*(-(a:𝓞 K5) + (b:𝓞 K5) + 6*(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^16*(2*(a:𝓞 K5) + 3*(b:𝓞 K5) + 6*(c:𝓞 K5) + (d:𝓞 K5)) + ζ^15*(6*(a:𝓞 K5) + 4*(b:𝓞 K5) + (c:𝓞 K5) - 4*(d:𝓞 K5)) + ζ^14*(5*(a:𝓞 K5) + 3*(b:𝓞 K5) - 6*(c:𝓞 K5) - 10*(d:𝓞 K5)) + ζ^13*(-5*(b:𝓞 K5) - 10*(c:𝓞 K5) - 10*(d:𝓞 K5)) + ζ^12*(-5*(a:𝓞 K5) - 12*(b:𝓞 K5) - 6*(c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^11*(-7*(a:𝓞 K5) - 9*(b:𝓞 K5) + (c:𝓞 K5) + 6*(d:𝓞 K5)) + ζ^10*(-2*(a:𝓞 K5) - (b:𝓞 K5) + 6*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^9*(7*(b:𝓞 K5) + 6*(c:𝓞 K5) + 7*(d:𝓞 K5)) + ζ^8*(4*(b:𝓞 K5) + 2*(c:𝓞 K5) + (d:𝓞 K5)) + ζ^7*(-(b:𝓞 K5) - (c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^6*((a:𝓞 K5) + 2*(b:𝓞 K5) - 2*(c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^5*(7*(a:𝓞 K5) + 6*(b:𝓞 K5) - (c:𝓞 K5) - (d:𝓞 K5)) + ζ^4*(4*(a:𝓞 K5) + 7*(b:𝓞 K5)) + ζ^3*(-2*(a:𝓞 K5) - 3*(b:𝓞 K5)) + ζ^2*(-6*(a:𝓞 K5) - 11*(b:𝓞 K5)) + ζ*(-5*(a:𝓞 K5) - 5*(b:𝓞 K5))) * cyc

lemma kD1_3 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 3) * (X + ζ * Y) - ζ ^ 3 * (X + ζ ^ 4 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((5*a + 5*b - 5*c - 5*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((-5*a - 10*b + 5*c + 10*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((-5*a - 10*b + 5*c + 10*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (-5*(a:𝓞 K5) - 5*(b:𝓞 K5) + 5*(c:𝓞 K5) - (d:𝓞 K5)*ζ^28 + 5*(d:𝓞 K5) + ζ^27*(-(b:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^26*(-2*(b:𝓞 K5) - (d:𝓞 K5)) + ζ^25*(-(b:𝓞 K5) + (d:𝓞 K5)) + ζ^24*((b:𝓞 K5) - (c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^23*(-(a:𝓞 K5) + 3*(b:𝓞 K5) - 2*(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^22*(-2*(a:𝓞 K5) + 2*(b:𝓞 K5) - (c:𝓞 K5) + (d:𝓞 K5)) + ζ^21*(-(a:𝓞 K5) + 2*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^20*(2*(a:𝓞 K5) + (b:𝓞 K5) + 6*(c:𝓞 K5) + 4*(d:𝓞 K5)) + ζ^19*(6*(a:𝓞 K5) + 3*(b:𝓞 K5) + 5*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^18*(5*(a:𝓞 K5) + 5*(b:𝓞 K5) - 5*(d:𝓞 K5)) + ζ^17*(-(a:𝓞 K5) - 5*(c:𝓞 K5) - 12*(d:𝓞 K5)) + ζ^16*(-7*(a:𝓞 K5) - 9*(b:𝓞 K5) - 7*(c:𝓞 K5) - 9*(d:𝓞 K5)) + ζ^15*(-8*(a:𝓞 K5) - 10*(b:𝓞 K5) - 2*(c:𝓞 K5) - (d:𝓞 K5)) + ζ^14*((a:𝓞 K5) - 3*(b:𝓞 K5) + 7*(d:𝓞 K5)) + ζ^13*(8*(a:𝓞 K5) + 8*(b:𝓞 K5) + 4*(d:𝓞 K5)) + ζ^12*(6*(a:𝓞 K5) + 8*(b:𝓞 K5) - (d:𝓞 K5)) + ζ^11*(-3*(a:𝓞 K5) - 4*(b:𝓞 K5) + (c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^10*(-12*(a:𝓞 K5) - 11*(b:𝓞 K5) + 7*(c:𝓞 K5) + 6*(d:𝓞 K5)) + ζ^9*(-6*(a:𝓞 K5) - 7*(b:𝓞 K5) + 4*(c:𝓞 K5) + 7*(d:𝓞 K5)) + ζ^8*(5*(a:𝓞 K5) + 9*(b:𝓞 K5) - 2*(c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^7*(11*(a:𝓞 K5) + 17*(b:𝓞 K5) - 6*(c:𝓞 K5) - 11*(d:𝓞 K5)) + ζ^6*(7*(a:𝓞 K5) + 6*(b:𝓞 K5) - 5*(c:𝓞 K5) - 5*(d:𝓞 K5)) + ζ^5*(-6*(a:𝓞 K5) - 8*(b:𝓞 K5) + 5*(c:𝓞 K5) + 5*(d:𝓞 K5)) + ζ^4*(-7*(a:𝓞 K5) - 13*(b:𝓞 K5) + 5*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^3*(-(a:𝓞 K5) - (b:𝓞 K5)) + ζ^2*(5*(a:𝓞 K5) + 10*(b:𝓞 K5) - 5*(c:𝓞 K5) - 10*(d:𝓞 K5)) + ζ*(5*(a:𝓞 K5) + 5*(b:𝓞 K5) - 5*(c:𝓞 K5) - 5*(d:𝓞 K5))) * cyc

lemma kD2_3 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 3) * (X + ζ ^ 2 * Y) - ζ ^ 3 * (X + ζ ^ 3 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((5*a + 5*b - 5*c - 10*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((-5*a - 10*b + 10*c + 15*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((-5*a - 10*b + 10*c + 15*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (-5*(a:𝓞 K5) - 5*(b:𝓞 K5) + 5*(c:𝓞 K5) - (d:𝓞 K5)*ζ^29 - 2*(d:𝓞 K5)*ζ^28 + 10*(d:𝓞 K5) + ζ^27*(-(b:𝓞 K5) - (d:𝓞 K5)) + ζ^26*(-2*(b:𝓞 K5) + (d:𝓞 K5)) + ζ^25*(-(b:𝓞 K5) - (c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^24*((b:𝓞 K5) - 2*(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^23*(-(a:𝓞 K5) + 3*(b:𝓞 K5) - (c:𝓞 K5)) + ζ^22*(-2*(a:𝓞 K5) + 2*(b:𝓞 K5) + 2*(c:𝓞 K5) + (d:𝓞 K5)) + ζ^21*(-(a:𝓞 K5) + 6*(c:𝓞 K5) + 4*(d:𝓞 K5)) + ζ^20*(2*(a:𝓞 K5) + (b:𝓞 K5) + 5*(c:𝓞 K5) + 6*(d:𝓞 K5)) + ζ^19*(6*(a:𝓞 K5) + 3*(b:𝓞 K5) - (c:𝓞 K5) - (d:𝓞 K5)) + ζ^18*(5*(a:𝓞 K5) + 5*(b:𝓞 K5) - 7*(c:𝓞 K5) - 11*(d:𝓞 K5)) + ζ^17*(-(a:𝓞 K5) - 7*(c:𝓞 K5) - 12*(d:𝓞 K5)) + ζ^16*(-7*(a:𝓞 K5) - 9*(b:𝓞 K5) + 2*(c:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^15*(-8*(a:𝓞 K5) - 10*(b:𝓞 K5) + 7*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^14*((a:𝓞 K5) - 3*(b:𝓞 K5) + 3*(c:𝓞 K5) + 7*(d:𝓞 K5)) + ζ^13*(8*(a:𝓞 K5) + 8*(b:𝓞 K5) - 7*(c:𝓞 K5) - 6*(d:𝓞 K5)) + ζ^12*(6*(a:𝓞 K5) + 8*(b:𝓞 K5) - 11*(c:𝓞 K5) - 12*(d:𝓞 K5)) + ζ^11*(-3*(a:𝓞 K5) - 4*(b:𝓞 K5) - (d:𝓞 K5)) + ζ^10*(-12*(a:𝓞 K5) - 11*(b:𝓞 K5) + 11*(c:𝓞 K5) + 17*(d:𝓞 K5)) + ζ^9*(-6*(a:𝓞 K5) - 7*(b:𝓞 K5) + 12*(c:𝓞 K5) + 16*(d:𝓞 K5)) + ζ^8*(5*(a:𝓞 K5) + 9*(b:𝓞 K5) - (c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^7*(11*(a:𝓞 K5) + 17*(b:𝓞 K5) - 12*(c:𝓞 K5) - 18*(d:𝓞 K5)) + ζ^6*(7*(a:𝓞 K5) + 6*(b:𝓞 K5) - 6*(c:𝓞 K5) - 11*(d:𝓞 K5)) + ζ^5*(-6*(a:𝓞 K5) - 8*(b:𝓞 K5) + 5*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^4*(-7*(a:𝓞 K5) - 13*(b:𝓞 K5) + 10*(c:𝓞 K5) + 15*(d:𝓞 K5)) + ζ^3*(-(a:𝓞 K5) - (b:𝓞 K5)) + ζ^2*(5*(a:𝓞 K5) + 10*(b:𝓞 K5) - 10*(c:𝓞 K5) - 15*(d:𝓞 K5)) + ζ*(5*(a:𝓞 K5) + 5*(b:𝓞 K5) - 5*(c:𝓞 K5) - 10*(d:𝓞 K5))) * cyc

lemma kD1_4 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 4) * (X + ζ * Y) - ζ ^ 4 * (X + ζ ^ 4 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((5*a + 10*b + 5*c + 5*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((-10*a - 15*b - 5*c - 10*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((-10*a - 15*b - 5*c - 10*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (-5*(a:𝓞 K5) - 10*(b:𝓞 K5) - 5*(c:𝓞 K5) - (d:𝓞 K5)*ζ^32 - 5*(d:𝓞 K5) + ζ^31*(-(b:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^30*(-2*(b:𝓞 K5) - (d:𝓞 K5)) + ζ^29*(-(b:𝓞 K5) + (d:𝓞 K5)) + ζ^28*((b:𝓞 K5) - (c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^27*(-(a:𝓞 K5) + 3*(b:𝓞 K5) - 2*(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^26*(-2*(a:𝓞 K5) + 2*(b:𝓞 K5) - (c:𝓞 K5)) + ζ^25*(-(a:𝓞 K5) + 2*(c:𝓞 K5) + (d:𝓞 K5)) + ζ^24*(2*(a:𝓞 K5) + (b:𝓞 K5) + 6*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^23*(6*(a:𝓞 K5) + 3*(b:𝓞 K5) + 5*(c:𝓞 K5) + 5*(d:𝓞 K5)) + ζ^22*(5*(a:𝓞 K5) + 4*(b:𝓞 K5) - (c:𝓞 K5)) + ζ^21*(-(a:𝓞 K5) - 2*(b:𝓞 K5) - 7*(c:𝓞 K5) - 9*(d:𝓞 K5)) + ζ^20*(-7*(a:𝓞 K5) - 10*(b:𝓞 K5) - 8*(c:𝓞 K5) - 10*(d:𝓞 K5)) + ζ^19*(-8*(a:𝓞 K5) - 8*(b:𝓞 K5) + (c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^18*(2*(b:𝓞 K5) + 8*(c:𝓞 K5) + 8*(d:𝓞 K5)) + ζ^17*(6*(a:𝓞 K5) + 11*(b:𝓞 K5) + 6*(c:𝓞 K5) + 8*(d:𝓞 K5)) + ζ^16*(5*(a:𝓞 K5) + 7*(b:𝓞 K5) - 3*(c:𝓞 K5) - 4*(d:𝓞 K5)) + ζ^15*(-6*(b:𝓞 K5) - 12*(c:𝓞 K5) - 11*(d:𝓞 K5)) + ζ^14*(-4*(a:𝓞 K5) - 10*(b:𝓞 K5) - 6*(c:𝓞 K5) - 7*(d:𝓞 K5)) + ζ^13*(-3*(b:𝓞 K5) + 5*(c:𝓞 K5) + 9*(d:𝓞 K5)) + ζ^12*(2*(a:𝓞 K5) + 6*(b:𝓞 K5) + 11*(c:𝓞 K5) + 17*(d:𝓞 K5)) + ζ^11*(-2*(a:𝓞 K5) + 4*(b:𝓞 K5) + 7*(c:𝓞 K5) + 6*(d:𝓞 K5)) + ζ^10*(-6*(a:𝓞 K5) - 7*(b:𝓞 K5) - 6*(c:𝓞 K5) - 8*(d:𝓞 K5)) + ζ^9*(-5*(a:𝓞 K5) - 6*(b:𝓞 K5) - 7*(c:𝓞 K5) - 13*(d:𝓞 K5)) + ζ^8*(6*(a:𝓞 K5) + 7*(b:𝓞 K5) - (c:𝓞 K5) - (d:𝓞 K5)) + ζ^7*(12*(a:𝓞 K5) + 16*(b:𝓞 K5) + 5*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^6*(4*(a:𝓞 K5) + 7*(b:𝓞 K5) + 5*(c:𝓞 K5) + 5*(d:𝓞 K5)) + ζ^5*(-7*(a:𝓞 K5) - 13*(b:𝓞 K5) - 5*(c:𝓞 K5) - 5*(d:𝓞 K5)) + ζ^4*(-11*(a:𝓞 K5) - 16*(b:𝓞 K5) - 5*(c:𝓞 K5) - 10*(d:𝓞 K5)) + ζ^2*(10*(a:𝓞 K5) + 15*(b:𝓞 K5) + 5*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ*(5*(a:𝓞 K5) + 10*(b:𝓞 K5) + 5*(c:𝓞 K5) + 5*(d:𝓞 K5))) * cyc

lemma kD2_4 (a b c d : ℤ) {X Y : 𝓞 K5} (hX : X = a + b * φ) (hY : Y = c + d * φ) :
    (ζ ^ (4 * 4) * (X + ζ ^ 2 * Y) - ζ ^ 4 * (X + ζ ^ 3 * Y)) * lam ^ 3 * u5 ^ 2 =
    ((5*a + 10*b - 5*c - 5*d : ℤ) : 𝓞 K5) * ζ ^ 0 + ((0 : ℤ) : 𝓞 K5) * ζ ^ 1 + ((-10*a - 15*b + 5*c + 10*d : ℤ) : 𝓞 K5) * ζ ^ 2 + ((-10*a - 15*b + 5*c + 10*d : ℤ) : 𝓞 K5) * ζ ^ 3 := by
  subst hX hY; push_cast
  linear_combination (-5*(a:𝓞 K5) - 10*(b:𝓞 K5) + 5*(c:𝓞 K5) - (d:𝓞 K5)*ζ^33 - 2*(d:𝓞 K5)*ζ^32 + 5*(d:𝓞 K5) + ζ^31*(-(b:𝓞 K5) - (d:𝓞 K5)) + ζ^30*(-2*(b:𝓞 K5) + (d:𝓞 K5)) + ζ^29*(-(b:𝓞 K5) - (c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^28*((b:𝓞 K5) - 2*(c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^27*(-(a:𝓞 K5) + 3*(b:𝓞 K5) - (c:𝓞 K5)) + ζ^26*(-2*(a:𝓞 K5) + 2*(b:𝓞 K5) + 2*(c:𝓞 K5) + (d:𝓞 K5)) + ζ^25*(-(a:𝓞 K5) + 6*(c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^24*(2*(a:𝓞 K5) + (b:𝓞 K5) + 5*(c:𝓞 K5) + 4*(d:𝓞 K5)) + ζ^23*(6*(a:𝓞 K5) + 3*(b:𝓞 K5) - (c:𝓞 K5) - 2*(d:𝓞 K5)) + ζ^22*(5*(a:𝓞 K5) + 4*(b:𝓞 K5) - 7*(c:𝓞 K5) - 9*(d:𝓞 K5)) + ζ^21*(-(a:𝓞 K5) - 2*(b:𝓞 K5) - 8*(c:𝓞 K5) - 7*(d:𝓞 K5)) + ζ^20*(-7*(a:𝓞 K5) - 10*(b:𝓞 K5) + (d:𝓞 K5)) + ζ^19*(-8*(a:𝓞 K5) - 8*(b:𝓞 K5) + 6*(c:𝓞 K5) + 9*(d:𝓞 K5)) + ζ^18*(2*(b:𝓞 K5) + 6*(c:𝓞 K5) + 5*(d:𝓞 K5)) + ζ^17*(6*(a:𝓞 K5) + 11*(b:𝓞 K5) + (c:𝓞 K5) - 5*(d:𝓞 K5)) + ζ^16*(5*(a:𝓞 K5) + 7*(b:𝓞 K5) - 5*(c:𝓞 K5) - 8*(d:𝓞 K5)) + ζ^15*(-6*(b:𝓞 K5) - 3*(c:𝓞 K5) - 4*(d:𝓞 K5)) + ζ^14*(-4*(a:𝓞 K5) - 10*(b:𝓞 K5) - 2*(c:𝓞 K5) + 4*(d:𝓞 K5)) + ζ^13*(-3*(b:𝓞 K5) - (c:𝓞 K5) + 3*(d:𝓞 K5)) + ζ^12*(2*(a:𝓞 K5) + 6*(b:𝓞 K5) - (d:𝓞 K5)) + ζ^11*(-2*(a:𝓞 K5) + 4*(b:𝓞 K5) + (c:𝓞 K5) + 2*(d:𝓞 K5)) + ζ^10*(-6*(a:𝓞 K5) - 7*(b:𝓞 K5) + 7*(c:𝓞 K5) + 6*(d:𝓞 K5)) + ζ^9*(-5*(a:𝓞 K5) - 6*(b:𝓞 K5) + 4*(c:𝓞 K5) + 7*(d:𝓞 K5)) + ζ^8*(6*(a:𝓞 K5) + 7*(b:𝓞 K5) - 2*(c:𝓞 K5) - 3*(d:𝓞 K5)) + ζ^7*(12*(a:𝓞 K5) + 16*(b:𝓞 K5) - 6*(c:𝓞 K5) - 11*(d:𝓞 K5)) + ζ^6*(4*(a:𝓞 K5) + 7*(b:𝓞 K5) - 5*(c:𝓞 K5) - 5*(d:𝓞 K5)) + ζ^5*(-7*(a:𝓞 K5) - 13*(b:𝓞 K5) + 5*(c:𝓞 K5) + 5*(d:𝓞 K5)) + ζ^4*(-11*(a:𝓞 K5) - 16*(b:𝓞 K5) + 5*(c:𝓞 K5) + 10*(d:𝓞 K5)) + ζ^2*(10*(a:𝓞 K5) + 15*(b:𝓞 K5) - 5*(c:𝓞 K5) - 10*(d:𝓞 K5)) + ζ*(5*(a:𝓞 K5) + 10*(b:𝓞 K5) - 5*(c:𝓞 K5) - 5*(d:𝓞 K5))) * cyc


/-- **Mod `λ⁵` forcing of the roots of unity.** -/
theorem kforce {X Y : 𝓞 K5} (hX : σ X = X) (hY : σ Y = Y) (hlX : ¬ lam ∣ X) (hlY : ¬ lam ∣ Y)
    (hlXY : ¬ lam ∣ X + Y) {k1 k2 : ℕ}
    (h1 : lam ^ 5 ∣ ζ ^ (4 * k1) * (X + ζ * Y) - ζ ^ k1 * (X + ζ ^ 4 * Y))
    (h2 : lam ^ 5 ∣ ζ ^ (4 * k2) * (X + ζ ^ 2 * Y) - ζ ^ k2 * (X + ζ ^ 3 * Y)) :
    k1 % 5 = 3 ∧ k2 % 5 = 1 := by
  obtain ⟨a, b, hab⟩ := real_form hX
  obtain ⟨c, d, hcd⟩ := real_form hY
  have nX := not_five_of_real hab hlX
  have nY := not_five_of_real hcd hlY
  have nXY := not_five_of_real (X := X + Y) (a := a + c) (b := b + d)
    (by rw [hab, hcd]; push_cast; ring) hlXY
  rw [show ζ ^ (4 * k1) = ζ ^ (4 * (k1 % 5)) from ζ_pow_eq_of_mod (by omega),
    show ζ ^ k1 = ζ ^ (k1 % 5) from ζ_pow_eq_of_mod (by omega)] at h1
  rw [show ζ ^ (4 * k2) = ζ ^ (4 * (k2 % 5)) from ζ_pow_eq_of_mod (by omega),
    show ζ ^ k2 = ζ ^ (k2 % 5) from ζ_pow_eq_of_mod (by omega)] at h2
  have hm1 : k1 % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hm2 : k2 % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize k1 % 5 = m1 at h1 hm1 ⊢
  generalize k2 % 5 = m2 at h2 hm2 ⊢
  have H1 := lam5_to_25 h1
  have H2 := lam5_to_25 h2
  interval_cases m1 <;> interval_cases m2
  all_goals first
    | exact ⟨rfl, rfl⟩
    | (exfalso
       first
       | (rw [kD1_0 a b c d hab hcd] at H1) | (rw [kD1_1 a b c d hab hcd] at H1)
       | (rw [kD1_2 a b c d hab hcd] at H1) | (rw [kD1_3 a b c d hab hcd] at H1)
       | (rw [kD1_4 a b c d hab hcd] at H1)
       first
       | (rw [kD2_0 a b c d hab hcd] at H2) | (rw [kD2_1 a b c d hab hcd] at H2)
       | (rw [kD2_2 a b c d hab hcd] at H2) | (rw [kD2_3 a b c d hab hcd] at H2)
       | (rw [kD2_4 a b c d hab hcd] at H2)
       obtain ⟨e0, e1, e2, e3⟩ := dvd25_coords H1
       obtain ⟨f0, f1, f2, f3⟩ := dvd25_coords H2
       omega)

end KForce

end OMA672Z5

-- ===== CaseA3.lean =====

open NumberField

namespace OMA672Z5

section Realify

lemma σσ (x : 𝓞 K5) : σ (σ x) = x := by
  rw [← τ_four_eq_σ, ← τ_four_eq_σ, ← RingHom.comp_apply, τ_comp (hab := by norm_num),
    τ_mod (a := 4 * 4) (b := 1) (by norm_num) (by norm_num) (by norm_num), τ_one]; rfl

lemma ζ_ne_zero : ζ ≠ 0 := fun h0 => by simpa [h0] using ζ_pow_five

lemma σ_zeta_pow (c : ℕ) : σ (ζ ^ c) = ζ ^ (4 * c) := by rw [map_pow, σ_ζ, ← pow_mul]

/-- A real element `e t⁵` with `e` a unit: `e` is real and `t` may be taken real. -/
theorem realify {w : 𝓞 K5} (hw : σ w = w) (hw0 : w ≠ 0) {e : (𝓞 K5)ˣ} {t : 𝓞 K5}
    (h : w = e * t ^ 5) : σ (e : 𝓞 K5) = e ∧ ∃ R : 𝓞 K5, σ R = R ∧ w = e * R ^ 5 := by
  have ht0 : t ≠ 0 := by rintro rfl; apply hw0; rw [h]; ring
  have hσw : (σ (e : 𝓞 K5)) * (σ t) ^ 5 = e * t ^ 5 := by
    rw [← map_pow, ← map_mul, ← h, hw]
  have hσe : IsUnit (σ (e : 𝓞 K5)) := e.isUnit.map σ
  have hd1 : t ∣ σ t := by
    apply (IsIntegrallyClosed.pow_dvd_pow_iff (by norm_num : (5 : ℕ) ≠ 0)).mp
    obtain ⟨v, hv⟩ := hσe.exists_left_inv
    exact ⟨v * e, by linear_combination (-(σ t) ^ 5) * hv + v * hσw⟩
  have hd2 : σ t ∣ t := by
    apply (IsIntegrallyClosed.pow_dvd_pow_iff (by norm_num : (5 : ℕ) ≠ 0)).mp
    obtain ⟨v, hv⟩ := e.isUnit.exists_left_inv
    exact ⟨v * σ (e : 𝓞 K5), by linear_combination (-t ^ 5) * hv - v * hσw⟩
  obtain ⟨v, hv⟩ := associated_of_dvd_dvd hd1 hd2
  -- `v σ v = 1`
  have hvv : (v : 𝓞 K5) * σ (v : 𝓞 K5) = 1 := by
    have h1 := congrArg σ hv
    rw [map_mul, σσ, ← hv] at h1
    exact mul_left_cancel₀ ht0 (by linear_combination h1)
  obtain ⟨c, r, hvr, hrσ⟩ := unit_decomp v
  have hr2 : r ^ 2 = 1 := by
    rw [hvr, map_mul, hrσ, σ_zeta_pow] at hvv
    have : ζ ^ c * ζ ^ (4 * c) = 1 := by
      rw [← pow_add, show c + 4 * c = 5 * c by ring, pow_mul, ζ_pow_five, one_pow]
    linear_combination hvv - r ^ 2 * this
  have hr : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.mp this with h' | h'
    · left; linear_combination h'
    · right; linear_combination h'
  set t' := ζ ^ (3 * c) * t with ht'
  have ht'5 : t' ^ 5 = t ^ 5 := by
    rw [ht', mul_pow, ← pow_mul, show 3 * c * 5 = 5 * (3 * c) by ring, pow_mul, ζ_pow_five,
      one_pow, one_mul]
  have hσt' : σ t' = r * t' := by
    rw [ht', map_mul, σ_zeta_pow, ← hv, hvr]
    have : ζ ^ (4 * (3 * c)) * ζ ^ c = ζ ^ (3 * c) := by
      rw [← pow_add]; exact ζ_pow_eq_of_mod (by omega)
    linear_combination (r * t) * this
  have hw' : w = e * t' ^ 5 := by rw [ht'5]; exact h
  have ht'0 : t' ^ 5 ≠ 0 := by rw [ht'5]; exact pow_ne_zero _ ht0
  rcases hr with rfl | rfl
  · rw [one_mul] at hσt'
    have hσe' : σ (e : 𝓞 K5) = e := by
      have := hσw; rw [← ht'5, ← map_pow, ← ht'5] at this
      rw [map_pow, hσt'] at this
      exact mul_right_cancel₀ ht'0 this
    exact ⟨hσe', t', hσt', hw'⟩
  · exfalso
    have h1 : σ (e : 𝓞 K5) = -e := by
      have := hσw; rw [← ht'5, ← map_pow, ← ht'5, map_pow, hσt'] at this
      have : (-σ (e : 𝓞 K5)) * t' ^ 5 = e * t' ^ 5 := by linear_combination this
      have := mul_right_cancel₀ ht'0 this; linear_combination -this
    obtain ⟨a, s, hes, hsσ⟩ := unit_decomp e
    rw [hes, map_mul, hsσ, σ_zeta_pow] at h1
    have hs0 : s ≠ 0 := by
      intro h0; have := e.ne_zero; rw [hes, h0, mul_zero] at this; exact this rfl
    have h2 : ζ ^ (4 * a) = -ζ ^ a := mul_right_cancel₀ hs0 (by linear_combination h1)
    have h3 : (ζ ^ (4 * a)) ^ 5 = (-ζ ^ a) ^ 5 := by rw [h2]
    rw [← pow_mul, show 4 * a * 5 = 5 * (4 * a) by ring, pow_mul, ζ_pow_five, one_pow, neg_pow,
      ← pow_mul, show a * 5 = 5 * a by ring, pow_mul, ζ_pow_five, one_pow] at h3
    have : (2 : 𝓞 K5) = 0 := by linear_combination h3
    exact two_ne_zero this

end Realify

section Factors

lemma factor_coprime {x y : 𝓞 K5} (hcop : IsCoprime x y) {r s : ℕ} (hrs : r < s) (hs : s < 5)
    (hl : ¬ lam ∣ x + ζ ^ r * y) : IsCoprime (x + ζ ^ r * y) (x + ζ ^ s * y) := by
  obtain ⟨w, hw, hdiff⟩ := diff_eq hrs hs
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨W, hW⟩ := hw.exists_left_inv
  have hlam : lam = (x + ζ ^ r * y) * (W * (u * ζ ^ s - v)) + (x + ζ ^ s * y) * (W * (v - u * ζ ^ r)) := by
    have : lam * w = (x + ζ ^ r * y) * (u * ζ ^ s - v) + (x + ζ ^ s * y) * (v - u * ζ ^ r) := by
      rw [← hdiff]; linear_combination (ζ ^ s - ζ ^ r) * huv.symm
    calc lam = W * (lam * w) := by linear_combination (-lam) * hW
      _ = _ := by rw [this]; ring
  obtain ⟨a, b, hab⟩ := ((Prime.coprime_iff_not_dvd lam_prime).mpr hl).symm
  refine ⟨a + b * (W * (u * ζ ^ s - v)), b * (W * (v - u * ζ ^ r)), ?_⟩
  rw [← hab, hlam]; ring

lemma lam_factor {x y : 𝓞 K5} (h : ¬ lam ∣ x + y) (i : ℕ) : ¬ lam ∣ x + ζ ^ i * y := by
  intro h1; apply h
  have hz : lam ∣ ζ ^ i - 1 := by
    have := sub_dvd_pow_sub_pow ζ 1 i; rw [one_pow] at this
    exact dvd_trans ⟨-1, by ring⟩ this
  have := dvd_sub h1 (dvd_mul_of_dvd_left hz y)
  convert this using 1; ring

lemma all_coprime {x y : 𝓞 K5} (hcop : IsCoprime x y) (h : ¬ lam ∣ x + y) :
    ∀ r s, r < s → s < 5 → IsCoprime (x + ζ ^ r * y) (x + ζ ^ s * y) :=
  fun _ _ hrs hs => factor_coprime hcop hrs hs (lam_factor h _)

lemma two_not_dvd_lam_mul {w y : 𝓞 K5} (hw : IsUnit w) (h : (2 : 𝓞 K5) ∣ lam * w * y) :
    (2 : 𝓞 K5) ∣ y := by
  rcases two_prime.dvd_or_dvd h with ha | ha
  · rcases two_prime.dvd_or_dvd ha with hb | hb
    · exfalso
      have : (2 : 𝓞 K5) ∣ ((1 : ℤ) : 𝓞 K5) + ((-1 : ℤ) : 𝓞 K5) * ζ + ((0 : ℤ) : 𝓞 K5) * ζ ^ 2
          + ((0 : ℤ) : 𝓞 K5) * ζ ^ 3 := by
        convert hb using 1; push_cast; ring
      have := (two_dvd_coord this).1; norm_num at this
    · exfalso; exact two_prime.not_unit (isUnit_of_dvd_unit hb hw)
  · exact ha

/-- Odd factors for real `X, Y`. -/
lemma two_not_dvd_real_factor {X Y : 𝓞 K5} (hX : σ X = X) (hY : σ Y = Y) (hcop : IsCoprime X Y)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 5) : ¬ (2 : 𝓞 K5) ∣ X + ζ ^ i * Y := by
  intro h
  have hσ : (2 : 𝓞 K5) ∣ X + ζ ^ (4 * i) * Y := by
    obtain ⟨t, ht⟩ := h
    exact ⟨σ t, by rw [← σ_zeta_pow, ← hX, ← hY, ← map_mul, ← map_add, ht, map_mul, map_ofNat]⟩
  have hdiff : (2 : 𝓞 K5) ∣ (ζ ^ i - ζ ^ (4 * i)) * Y := by
    have := dvd_sub h hσ; convert this using 1; ring
  obtain ⟨w, hw, hw'⟩ := one_sub_pow_eq ((3 * i) % 5) (by omega)
  have he : ζ ^ i - ζ ^ (4 * i) = lam * (ζ ^ i * w) := by
    have : ζ ^ (4 * i) = ζ ^ i * ζ ^ ((3 * i) % 5) := by
      rw [← pow_add]; exact ζ_pow_eq_of_mod (by omega)
    rw [this]; linear_combination ζ ^ i * hw'
  rw [he] at hdiff
  have h2Y := two_not_dvd_lam_mul (((ζ_prim.isUnit (by norm_num)).pow i).mul hw) hdiff
  have h2X : (2 : 𝓞 K5) ∣ X := by
    have := dvd_sub h (dvd_mul_of_dvd_right h2Y (ζ ^ i)); convert this using 1; ring
  exact two_prime.not_unit (hcop.isUnit_of_dvd' h2X h2Y)

lemma two_val {γ : 𝓞 K5} (h0 : γ ≠ 0) : ∃ a : ℕ, ∃ g : 𝓞 K5, γ = 2 ^ a * g ∧ ¬ (2 : 𝓞 K5) ∣ g := by
  obtain ⟨g, hg, hg2⟩ :=
    (FiniteMultiplicity.of_not_isUnit two_prime.not_unit h0).exists_eq_pow_mul_and_not_dvd
  exact ⟨_, g, hg, hg2⟩

lemma two_pow_cancel {a b : ℕ} {u v : 𝓞 K5} (hu : ¬ (2 : 𝓞 K5) ∣ u) (hv : ¬ (2 : 𝓞 K5) ∣ v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have h2 : (2 : 𝓞 K5) ≠ 0 := two_ne_zero
  rcases le_total a b with hab | hab
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (pow_ne_zero a h2) h
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at h'; exact ⟨by simp, h'⟩
    · exfalso; apply hu; rw [h']
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 hc.ne') _
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (pow_ne_zero b h2) h
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at h'; exact ⟨by simp, h'⟩
    · exfalso; apply hv; rw [← h']
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 hc.ne') _

lemma assoc_of_pow5 {a b : 𝓞 K5} {E : (𝓞 K5)ˣ} (h : a ^ 5 = E * b ^ 5) : Associated a b := by
  apply associated_of_dvd_dvd
  · apply (IsIntegrallyClosed.pow_dvd_pow_iff (by norm_num : (5 : ℕ) ≠ 0)).mp
    refine ⟨↑E⁻¹, ?_⟩
    rw [h, mul_comm (E : 𝓞 K5), mul_assoc, Units.mul_inv, mul_one]
  · apply (IsIntegrallyClosed.pow_dvd_pow_iff (by norm_num : (5 : ℕ) ≠ 0)).mp
    exact ⟨E, by rw [h, mul_comm]⟩

lemma two_dvd_four {a b c d : 𝓞 K5} (h : (2 : 𝓞 K5) ∣ a * b * c * d) :
    (2 : 𝓞 K5) ∣ a ∨ (2 : 𝓞 K5) ∣ b ∨ (2 : 𝓞 K5) ∣ c ∨ (2 : 𝓞 K5) ∣ d := by
  rcases two_prime.dvd_or_dvd h with h1 | h1
  · rcases two_prime.dvd_or_dvd h1 with h2 | h2
    · rcases two_prime.dvd_or_dvd h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr h1))

/-- **Factor structure** of `x⁵ + y⁵ = E 2^j W⁵` with coprime conjugate factors, odd except `x + y`. -/
theorem five_factor {x y W : 𝓞 K5} {E : (𝓞 K5)ˣ} {j : ℕ} (hW0 : W ≠ 0)
    (hcop : ∀ r s, r < s → s < 5 → IsCoprime (x + ζ ^ r * y) (x + ζ ^ s * y))
    (hodd : ∀ i, 1 ≤ i → i < 5 → ¬ (2 : 𝓞 K5) ∣ x + ζ ^ i * y)
    (h : x ^ 5 + y ^ 5 = E * 2 ^ j * W ^ 5) :
    ∃ e0 e1 e2 e3 e4 : (𝓞 K5)ˣ, ∃ R0 t1 t2 t3 t4 : 𝓞 K5,
      x + y = 2 ^ j * e0 * R0 ^ 5 ∧ x + ζ * y = e1 * t1 ^ 5 ∧ x + ζ ^ 2 * y = e2 * t2 ^ 5 ∧
      x + ζ ^ 3 * y = e3 * t3 ^ 5 ∧ x + ζ ^ 4 * y = e4 * t4 ^ 5 ∧
      Associated (R0 * t1 * t2 * t3 * t4) W := by
  set g0 := x + y
  set g1 := x + ζ * y
  set g2 := x + ζ ^ 2 * y
  set g3 := x + ζ ^ 3 * y
  set g4 := x + ζ ^ 4 * y
  have hp : g0 * g1 * g2 * g3 * g4 = E * 2 ^ j * W ^ 5 := by rw [← h]; exact prod_five x y
  have c01 : IsCoprime g0 g1 := by simpa using hcop 0 1 (by norm_num) (by norm_num)
  have c02 : IsCoprime g0 g2 := by simpa using hcop 0 2 (by norm_num) (by norm_num)
  have c03 : IsCoprime g0 g3 := by simpa using hcop 0 3 (by norm_num) (by norm_num)
  have c04 : IsCoprime g0 g4 := by simpa using hcop 0 4 (by norm_num) (by norm_num)
  have c12 : IsCoprime g1 g2 := by simpa using hcop 1 2 (by norm_num) (by norm_num)
  have c13 : IsCoprime g1 g3 := by simpa using hcop 1 3 (by norm_num) (by norm_num)
  have c14 : IsCoprime g1 g4 := by simpa using hcop 1 4 (by norm_num) (by norm_num)
  have c23 : IsCoprime g2 g3 := hcop 2 3 (by norm_num) (by norm_num)
  have c24 : IsCoprime g2 g4 := hcop 2 4 (by norm_num) (by norm_num)
  have c34 : IsCoprime g3 g4 := hcop 3 4 (by norm_num) (by norm_num)
  have o1 : ¬ (2 : 𝓞 K5) ∣ g1 := by simpa using hodd 1 (by norm_num) (by norm_num)
  have o2 : ¬ (2 : 𝓞 K5) ∣ g2 := hodd 2 (by norm_num) (by norm_num)
  have o3 : ¬ (2 : 𝓞 K5) ∣ g3 := hodd 3 (by norm_num) (by norm_num)
  have o4 : ¬ (2 : 𝓞 K5) ∣ g4 := hodd 4 (by norm_num) (by norm_num)
  obtain ⟨t1, e1, h1⟩ := fifth_of_coprime (R := g0 * g2 * g3 * g4)
    (((c01.symm.mul_right c12).mul_right c13).mul_right c14) o1 (by rw [← hp]; ring)
  obtain ⟨t2, e2, h2⟩ := fifth_of_coprime (R := g0 * g1 * g3 * g4)
    (((c02.symm.mul_right c12.symm).mul_right c23).mul_right c24) o2 (by rw [← hp]; ring)
  obtain ⟨t3, e3, h3⟩ := fifth_of_coprime (R := g0 * g1 * g2 * g4)
    (((c03.symm.mul_right c13.symm).mul_right c23.symm).mul_right c34) o3 (by rw [← hp]; ring)
  obtain ⟨t4, e4, h4⟩ := fifth_of_coprime (R := g0 * g1 * g2 * g3)
    (((c04.symm.mul_right c14.symm).mul_right c24.symm).mul_right c34.symm) o4 (by rw [← hp]; ring)
  have hg0 : g0 ≠ 0 := by
    intro h0
    apply mul_ne_zero (mul_ne_zero E.ne_zero (pow_ne_zero j two_ne_zero)) (pow_ne_zero 5 hW0)
    rw [← hp, h0]; ring
  obtain ⟨a, g, hag, hg2⟩ := two_val hg0
  obtain ⟨t, W1, htW, hW12⟩ := two_val hW0
  have hP2 : ¬ (2 : 𝓞 K5) ∣ g * (g1 * g2 * g3 * g4) := by
    intro hd
    rcases two_prime.dvd_or_dvd hd with ha | ha
    · exact hg2 ha
    · rcases two_dvd_four ha with hb | hb | hb | hb
      · exact o1 hb
      · exact o2 hb
      · exact o3 hb
      · exact o4 hb
  have hEW : ¬ (2 : 𝓞 K5) ∣ E * W1 ^ 5 := by
    intro hd
    rcases two_prime.dvd_or_dvd hd with ha | ha
    · exact two_prime.not_unit (isUnit_of_dvd_unit ha E.isUnit)
    · exact hW12 (two_prime.dvd_of_dvd_pow ha)
  have heq : 2 ^ a * (g * (g1 * g2 * g3 * g4)) = 2 ^ (j + 5 * t) * (E * W1 ^ 5) := by
    calc 2 ^ a * (g * (g1 * g2 * g3 * g4)) = g0 * g1 * g2 * g3 * g4 := by rw [hag]; ring
      _ = E * 2 ^ j * W ^ 5 := hp
      _ = _ := by rw [htW]; ring
  obtain ⟨ha, hgP⟩ := two_pow_cancel hP2 hEW heq
  have cgP : IsCoprime g (g1 * g2 * g3 * g4) := by
    have : IsCoprime g0 (g1 * g2 * g3 * g4) := ((c01.mul_right c02).mul_right c03).mul_right c04
    exact this.of_isCoprime_of_dvd_left ⟨2 ^ a, by rw [hag]; ring⟩
  obtain ⟨s, e0, hs⟩ := fifth_of_coprime (j := 0) (E := E) (w := W1) cgP hg2 (by rw [hgP]; ring)
  refine ⟨e0, e1, e2, e3, e4, 2 ^ t * s, t1, t2, t3, t4, ?_, h1, h2, h3, h4, ?_⟩
  · rw [hag, ha, hs]; ring
  · set U := e0 * e1 * e2 * e3 * e4
    set A := 2 ^ t * s * t1 * t2 * t3 * t4
    apply assoc_of_pow5 (E := U⁻¹ * E)
    have hprod : (2 : 𝓞 K5) ^ j * ((U : 𝓞 K5) * A ^ 5) = 2 ^ j * (E * W ^ 5) := by
      calc (2 : 𝓞 K5) ^ j * ((U : 𝓞 K5) * A ^ 5) = g0 * g1 * g2 * g3 * g4 := by
            rw [hag, ha, hs, h1, h2, h3, h4]; simp only [U, A, Units.val_mul]; ring
        _ = _ := by rw [hp]; ring
    have h2j : (2 : 𝓞 K5) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero
    have hUA := mul_left_cancel₀ h2j hprod
    calc A ^ 5 = (↑U⁻¹ : 𝓞 K5) * ((U : 𝓞 K5) * A ^ 5) := by rw [← mul_assoc]; simp
      _ = _ := by rw [hUA, Units.val_mul]; ring

end Factors

section Back

lemma lam_dvd_σ_of {n : ℕ} {x : 𝓞 K5} (h : lam ^ n ∣ x) : lam ^ n ∣ σ x := by
  obtain ⟨t, rfl⟩ := h
  have hσ : σ lam = lam * (-ζ ^ 4) := by
    rw [map_sub, map_one, σ_ζ]; linear_combination (-1 : 𝓞 K5) * ζ_pow_five
  rw [map_mul, map_pow, hσ, mul_pow, mul_assoc]
  exact dvd_mul_right _ _

lemma lam5_conj (t : 𝓞 K5) : lam ^ 5 ∣ t ^ 5 - (σ t) ^ 5 := by
  obtain ⟨c, hc⟩ := exists_int_congr t
  have h1 := pow_five_congr hc
  have h2 : lam ∣ σ t - c := by
    have := lam_dvd_σ_of (n := 1) (x := t - c) (by rw [pow_one]; exact hc)
    rwa [pow_one, show σ (t - (c : 𝓞 K5)) = σ t - c by rw [map_sub, map_intCast]] at this
  have h3 := pow_five_congr h2
  have := dvd_sub h1 h3
  convert this using 1; ring

lemma lam2_conj {x : 𝓞 K5} {c : ℤ} (h : lam ^ 2 ∣ x - c) : lam ^ 2 ∣ σ x - c := by
  have := lam_dvd_σ_of h; rwa [map_sub, map_intCast] at this

/-- The unit equation `v + w = 2` in `ℤ[φ]` with `v ≡ 1 (mod λ)`. -/
lemma unit_eq_two {v : 𝓞 K5} (hv : σ v = v) (hvu : IsUnit v) (hwu : IsUnit (2 - v))
    (hl : lam ∣ v - 1) : v = 1 := by
  obtain ⟨a, b, hab⟩ := real_form hv
  have hinv : ∀ x : 𝓞 K5, σ x = x → IsUnit x → ∃ a b a' b' : ℤ, x = a + b * φ ∧
      ((a : 𝓞 K5) + b * φ) * (a' + b' * φ) = 1 := by
    intro x hx hxu
    obtain ⟨y, hy⟩ := hxu.exists_right_inv
    have hyσ : σ y = y := by
      have h1 := congrArg σ hy; rw [map_mul, hx, map_one] at h1
      have : x * σ y = x * y := by rw [h1, hy]
      exact mul_left_cancel₀ (hxu.ne_zero) this
    obtain ⟨a, b, rfl⟩ := real_form hx
    obtain ⟨a', b', rfl⟩ := real_form hyσ
    exact ⟨a, b, a', b', rfl, hy⟩
  obtain ⟨a1, b1, a1', b1', hx1, hn1⟩ := hinv v hv hvu
  have hw : σ (2 - v) = 2 - v := by rw [map_sub, hv, map_ofNat]
  obtain ⟨a2, b2, a2', b2', hx2, hn2⟩ := hinv (2 - v) hw hwu
  have N1 := real_unit_norm hn1
  have N2 := real_unit_norm hn2
  have e1 := φcoord_eq (hab.symm.trans hx1)
  have e2 := φcoord_eq (x := 2 - a) (y := -b) (by rw [← hx2, hab]; push_cast; ring)
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  -- `λ ∣ v - 1` gives `5 ∣ a - 1 + 3b`
  have h5 : (5 : ℤ) ∣ a - 1 + 3 * b := by
    apply lam_dvd_int
    have h2 : lam ∣ φ - 3 := ⟨ζ ^ 4 * lam, by rw [phi_sub_three]; ring⟩
    have := dvd_sub hl (dvd_mul_of_dvd_right h2 (b : 𝓞 K5))
    rw [hab] at this; push_cast; convert this using 1; ring
  have h1 : -1 ≤ a ^ 2 + a * b - b ^ 2 ∧ a ^ 2 + a * b - b ^ 2 ≤ 1 := by
    rcases N1 with h | h <;> constructor <;> linarith
  have h2 : -2 ≤ 4 - 4 * a - 2 * b ∧ 4 - 4 * a - 2 * b ≤ 2 := by
    rcases N1 with h | h <;> rcases N2 with h' | h' <;> constructor <;> nlinarith
  have ha : a ≤ 3 ∧ -2 ≤ a := by
    constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (2 * a + b - 2)]
  have key : a = 1 ∧ b = 0 := by
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨h21, h22⟩ := h2
    have hb1 : b ≤ 7 := by omega
    have hb2 : -5 ≤ b := by omega
    interval_cases a <;> interval_cases b <;> first | exact ⟨rfl, rfl⟩ | (exfalso; omega) |
      (exfalso; rcases N1 with h | h <;> rcases N2 with h' | h' <;> norm_num at h h' <;> omega)
  rw [hab, key.1, key.2]; simp

/-- If `X + ζ Y = ζ³ u` with `X, Y, u` real then `X = Y`. -/
lemma eq_of_unit_form {X Y u : 𝓞 K5} (hX : σ X = X) (hY : σ Y = Y) (hu : σ u = u)
    (h : X + ζ * Y = ζ ^ 3 * u) : X = Y := by
  have h4 : X + ζ ^ 4 * Y = ζ ^ 2 * u := by
    have := congrArg σ h
    rw [map_add, map_mul, hX, hY, σ_ζ, map_mul, σ_zeta_pow, hu] at this
    rw [this, show ζ ^ (4 * 3) = ζ ^ 2 from ζ_pow_eq_of_mod (by norm_num)]
  have hne : ζ - ζ ^ 4 ≠ 0 := by
    intro h0
    have : ζ ^ 1 = ζ ^ 4 := by rw [pow_one]; exact sub_eq_zero.mp h0
    have h3 : ζ ^ 3 = 1 := by
      apply mul_left_cancel₀ ζ_ne_zero
      linear_combination (-1 : 𝓞 K5) * this
    exact ζ_prim.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h3
  apply sub_eq_zero.mp
  apply mul_left_cancel₀ hne
  linear_combination (-ζ ^ 4 - 1) * h + (1 + ζ) * h4 - (u * ζ ^ 2) * ζ_pow_five

end Back

end OMA672Z5

-- ===== CaseA4.lean =====

open NumberField

namespace OMA672Z5

section Stage

lemma unit_decomp' (u : (𝓞 K5)ˣ) : ∃ k : ℕ, ∃ r : (𝓞 K5)ˣ, (u : 𝓞 K5) = ζ ^ k * r ∧ σ (r : 𝓞 K5) = r := by
  obtain ⟨k, w, hu, hw⟩ := unit_decomp u
  have hwu : IsUnit w := isUnit_of_mul_isUnit_right (hu ▸ u.isUnit)
  exact ⟨k, hwu.unit, by rw [hu, IsUnit.unit_spec], by rw [IsUnit.unit_spec]; exact hw⟩

lemma absNorm_mul' (a b : 𝓞 K5) :
    Ideal.absNorm (Ideal.span {a * b}) = Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm (Ideal.span {b}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma absNorm_assoc {a b : 𝓞 K5} (h : Associated a b) :
    Ideal.absNorm (Ideal.span {a}) = Ideal.absNorm (Ideal.span {b}) := by
  rw [Ideal.span_singleton_eq_span_singleton.mpr h]

lemma absNorm_pos {a : 𝓞 K5} (h : a ≠ 0) : 0 < Ideal.absNorm (Ideal.span {a}) := by
  apply Nat.pos_of_ne_zero
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact h

lemma absNorm_eq_one {a : 𝓞 K5} : Ideal.absNorm (Ideal.span {a}) = 1 ↔ IsUnit a := by
  rw [Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]

lemma σ_pow_conj {k : ℕ} {r : 𝓞 K5} (hr : σ r = r) (t : 𝓞 K5) :
    σ (ζ ^ k * r * t ^ 5) = ζ ^ (4 * k) * r * (σ t) ^ 5 := by
  rw [map_mul, map_mul, σ_zeta_pow, map_pow, hr]

lemma lam5_pair {k : ℕ} {r : 𝓞 K5} (t : 𝓞 K5) :
    lam ^ 5 ∣ ζ ^ (4 * k) * (ζ ^ k * r * t ^ 5) - ζ ^ k * (ζ ^ (4 * k) * r * (σ t) ^ 5) := by
  have : ζ ^ (4 * k) * (ζ ^ k * r * t ^ 5) - ζ ^ k * (ζ ^ (4 * k) * r * (σ t) ^ 5)
      = (ζ ^ (4 * k) * ζ ^ k * r) * (t ^ 5 - (σ t) ^ 5) := by ring
  rw [this]; exact dvd_mul_of_dvd_right (lam5_conj t) _

lemma not_lam_sum {X Y Z : 𝓞 K5} {E : (𝓞 K5)ˣ} {j : ℕ} (hlZ : ¬ lam ∣ Z)
    (heq : X ^ 5 + Y ^ 5 = E * 2 ^ j * Z ^ 5) : ¬ lam ∣ X + Y := by
  intro h; apply hlZ
  have : lam ∣ E * 2 ^ j * Z ^ 5 := by
    rw [← heq, ← prod_five]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left h _) _) _) _
  rcases lam_prime.dvd_or_dvd this with h1 | h1
  · rcases lam_prime.dvd_or_dvd h1 with h2 | h2
    · exact absurd h2 (not_lam_dvd_unit E)
    · exact absurd h2 (not_lam_dvd_two_pow j)
  · exact lam_prime.dvd_of_dvd_pow h1

/-- Analysis of one real stage. -/
theorem stageR {j : ℕ} {X Y Z : 𝓞 K5} {E : (𝓞 K5)ˣ} (hX : σ X = X) (hY : σ Y = Y)
    (hcop : IsCoprime X Y) (hlX : ¬ lam ∣ X) (hlY : ¬ lam ∣ Y) (hlZ : ¬ lam ∣ Z)
    (heq : X ^ 5 + Y ^ 5 = E * 2 ^ j * Z ^ 5) :
    (∀ (a : ℕ) (w : (𝓞 K5)ˣ) (t : 𝓞 K5), σ (w : 𝓞 K5) = w → X + ζ * Y = ζ ^ a * w * t ^ 5 →
      a % 5 = 3) ∧
    ∃ r1 r2 r0 : (𝓞 K5)ˣ, ∃ t1 t2 W : 𝓞 K5, σ (r1 : 𝓞 K5) = r1 ∧ σ (r2 : 𝓞 K5) = r2 ∧
      σ (r0 : 𝓞 K5) = r0 ∧ σ W = W ∧ X + ζ * Y = ζ ^ 3 * r1 * t1 ^ 5 ∧
      X + ζ ^ 2 * Y = ζ * r2 * t2 ^ 5 ∧ X + Y = 2 ^ j * r0 * W ^ 5 ∧
      Ideal.absNorm (Ideal.span {W}) * Ideal.absNorm (Ideal.span {t1}) ≤
        Ideal.absNorm (Ideal.span {Z}) := by
  have hlXY := not_lam_sum hlZ heq
  have hZ0 : Z ≠ 0 := fun h => hlZ (h ▸ dvd_zero _)
  obtain ⟨e0, e1, e2, e3, e4, R0, t1, t2, t3, t4, h0, h1, h2, h3, h4, hass⟩ :=
    five_factor hZ0 (all_coprime hcop hlXY)
      (fun i hi1 hi => two_not_dvd_real_factor hX hY hcop hi1 hi) heq
  have hσ1 : σ (X + ζ * Y) = X + ζ ^ 4 * Y := by rw [map_add, map_mul, hX, hY, σ_ζ]
  have hσ2 : σ (X + ζ ^ 2 * Y) = X + ζ ^ 3 * Y := by
    rw [map_add, map_mul, hX, hY, σ_zeta_pow, show ζ ^ (4 * 2) = ζ ^ 3 from ζ_pow_eq_of_mod (by norm_num)]
  obtain ⟨k2, r2, he2, hr2⟩ := unit_decomp' e2
  have H2 : lam ^ 5 ∣ ζ ^ (4 * k2) * (X + ζ ^ 2 * Y) - ζ ^ k2 * (X + ζ ^ 3 * Y) := by
    have e2' : X + ζ ^ 2 * Y = ζ ^ k2 * r2 * t2 ^ 5 := by rw [h2, he2]
    rw [← hσ2, e2', σ_pow_conj hr2]; exact lam5_pair t2
  have kf : ∀ (a : ℕ) (w : (𝓞 K5)ˣ) (t : 𝓞 K5), σ (w : 𝓞 K5) = w →
      X + ζ * Y = ζ ^ a * w * t ^ 5 → a % 5 = 3 := by
    intro a w t hw ht
    have H1 : lam ^ 5 ∣ ζ ^ (4 * a) * (X + ζ * Y) - ζ ^ a * (X + ζ ^ 4 * Y) := by
      rw [← hσ1, ht, σ_pow_conj hw]; exact lam5_pair t
    exact (kforce hX hY hlX hlY hlXY H1 H2).1
  refine ⟨kf, ?_⟩
  obtain ⟨k1, r1, he1, hr1⟩ := unit_decomp' e1
  have e1' : X + ζ * Y = ζ ^ k1 * r1 * t1 ^ 5 := by rw [h1, he1]
  have H1 : lam ^ 5 ∣ ζ ^ (4 * k1) * (X + ζ * Y) - ζ ^ k1 * (X + ζ ^ 4 * Y) := by
    rw [← hσ1, e1', σ_pow_conj hr1]; exact lam5_pair t1
  obtain ⟨hk1, hk2⟩ := kforce hX hY hlX hlY hlXY H1 H2
  have z1 : ζ ^ k1 = ζ ^ 3 := ζ_pow_eq_of_mod (by omega)
  have z2 : ζ ^ k2 = ζ := by
    have : ζ ^ k2 = ζ ^ 1 := ζ_pow_eq_of_mod (by omega)
    rwa [pow_one] at this
  -- realify the even factor
  have hσw : σ ((e0 : 𝓞 K5) * R0 ^ 5) = e0 * R0 ^ 5 := by
    have hXY : σ (X + Y) = X + Y := by rw [map_add, hX, hY]
    rw [h0, mul_assoc, map_mul, map_pow, map_ofNat] at hXY
    exact mul_left_cancel₀ (pow_ne_zero j two_ne_zero) hXY
  have hw0 : (e0 : 𝓞 K5) * R0 ^ 5 ≠ 0 := by
    intro h; apply hlXY; rw [h0, mul_assoc, h, mul_zero]; exact dvd_zero _
  obtain ⟨hσe0, W, hσW, hW⟩ := realify hσw hw0 rfl
  have hWR : Associated W R0 := by
    apply assoc_of_pow5 (E := 1)
    rw [Units.val_one, one_mul]
    exact mul_left_cancel₀ e0.ne_zero hW.symm
  refine ⟨r1, r2, e0, t1, t2, W, hr1, hr2, hσe0, hσW, by rw [e1', z1], by rw [h2, he2, z2],
    by rw [h0, mul_assoc, hW, ← mul_assoc], ?_⟩
  rw [← absNorm_assoc hass, absNorm_assoc hWR, absNorm_mul', absNorm_mul', absNorm_mul',
    absNorm_mul']
  have p2 := absNorm_pos (a := t2) (by rintro rfl; exact hlXY (by
    have : X + ζ ^ 2 * Y = 0 := by rw [h2]; ring
    exact absurd (this ▸ dvd_zero lam) (lam_factor hlXY 2)))
  have p3 := absNorm_pos (a := t3) (by rintro rfl; exact absurd (by rw [h3]; simp : lam ∣ X + ζ ^ 3 * Y) (lam_factor hlXY 3))
  have p4 := absNorm_pos (a := t4) (by rintro rfl; exact absurd (by rw [h4]; simp : lam ∣ X + ζ ^ 4 * Y) (lam_factor hlXY 4))
  calc Ideal.absNorm (Ideal.span {R0}) * Ideal.absNorm (Ideal.span {t1})
      = Ideal.absNorm (Ideal.span {R0}) * Ideal.absNorm (Ideal.span {t1}) * 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr <;> omega

lemma unit_dvd_iff {u : 𝓞 K5} (hu : IsUnit u) {q x : 𝓞 K5} : u * q ∣ x ↔ q ∣ x :=
  hu.mul_left_dvd

/-- Every divisor of `t₁` is good. -/
theorem good_t1 {j : ℕ} (hj : j = 1 ∨ j = 3) {X Y : 𝓞 K5} (hX : σ X = X) (hY : σ Y = Y)
    (hcop : IsCoprime X Y) (hlXY : ¬ lam ∣ X + Y) {r1 r2 r0 : (𝓞 K5)ˣ} {t1 t2 W : 𝓞 K5}
    (hr2 : σ (r2 : 𝓞 K5) = r2) (hr0 : σ (r0 : 𝓞 K5) = r0)
    (h1 : X + ζ * Y = ζ ^ 3 * r1 * t1 ^ 5) (h2 : X + ζ ^ 2 * Y = ζ * r2 * t2 ^ 5)
    (h0 : X + Y = 2 ^ j * r0 * W ^ 5) : Good t1 := by
  have hcopall := all_coprime hcop hlXY
  have c12 : IsCoprime (X + ζ * Y) (X + ζ ^ 2 * Y) := by simpa using hcopall 1 2 (by norm_num) (by norm_num)
  have c13 : IsCoprime (X + ζ * Y) (X + ζ ^ 3 * Y) := by simpa using hcopall 1 3 (by norm_num) (by norm_num)
  have c01 : IsCoprime (X + Y) (X + ζ * Y) := by simpa using hcopall 0 1 (by norm_num) (by norm_num)
  have hlt1 : ¬ lam ∣ t1 := by
    intro h; apply lam_factor hlXY 1; rw [pow_one, h1]
    exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _
  have hσ2 : σ (X + ζ ^ 2 * Y) = X + ζ ^ 3 * Y := by
    rw [map_add, map_mul, hX, hY, σ_zeta_pow, show ζ ^ (4 * 2) = ζ ^ 3 from ζ_pow_eq_of_mod (by norm_num)]
  have h3 : X + ζ ^ 3 * Y = ζ ^ 4 * r2 * (σ t2) ^ 5 := by
    rw [← hσ2, h2, ← pow_one ζ, σ_pow_conj hr2]
    simp
  refine good_of_dvd hlt1 (fun q hq hqt => ?_) t1 dvd_rfl
  have hq1 : q ∣ X + ζ * Y := dvd_trans hqt ⟨ζ ^ 3 * r1 * t1 ^ 4, by rw [h1]; ring⟩
  have hnu : ∀ {z : 𝓞 K5}, IsCoprime (X + ζ * Y) z → ¬ q ∣ z := fun hc hz =>
    hq.not_unit (hc.isUnit_of_dvd' hq1 hz)
  have hql : ¬ q ∣ lam := by
    intro h
    have := (hq.associated_of_dvd lam_prime h).symm.dvd
    exact lam_factor hlXY 1 (by rw [pow_one]; exact dvd_trans this hq1)
  have hqY : ¬ q ∣ Y := by
    intro hy
    have hx : q ∣ X := by
      have := dvd_sub hq1 (dvd_mul_of_dvd_right hy ζ); simpa using this
    exact hq.not_unit (hcop.isUnit_of_dvd' hx hy)
  obtain ⟨n, hn⟩ := deg_one hq hql hX hY hqY hq1
  obtain ⟨p, hp, ψ, hd, hker⟩ := exists_psi hq hql hn
  have h2k := two_fifth_power ψ hd hr2 hr0 hj ((hker _).mpr hq1)
    (fun h => hqY ((hker _).mp h))
    (fun h => hnu c12 (dvd_trans ((hker _).mp h) ⟨ζ * r2 * t2 ^ 4, by rw [h2]; ring⟩))
    (fun h => hnu c13 (dvd_trans ((hker _).mp h) ⟨ζ ^ 4 * r2 * (σ t2) ^ 4, by rw [h3]; ring⟩))
    (fun h => hnu c01.symm (dvd_trans ((hker _).mp h) ⟨2 ^ j * r0 * W ^ 4, by rw [h0]; ring⟩))
    h2 h3 h0
  intro k c hkc
  have hu : IsUnit (ζ ^ k) := (ζ_prim.isUnit (by norm_num)).pow k
  exact eis2 ψ hd (π := ζ ^ k * q) (fun x => by rw [hker, unit_dvd_iff hu]) hkc h2k

end Stage

section StageP

lemma σ_unit_inv {u : (𝓞 K5)ˣ} (h : σ (u : 𝓞 K5) = u) : σ ((u⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = (u⁻¹ : (𝓞 K5)ˣ) := by
  have h1 : σ (u : 𝓞 K5) * σ ((u⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [h] at h1
  calc σ ((u⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = (u⁻¹ : (𝓞 K5)ˣ) * (u * σ ((u⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [h1, mul_one]

lemma lam_dvd_mul_unit {u : 𝓞 K5} (hu : IsUnit u) {x : 𝓞 K5} (h : lam ∣ u * x) : lam ∣ x := by
  obtain ⟨U, rfl⟩ := hu; exact (Units.dvd_mul_left).mp h

lemma lam3_dvd_125 : lam ^ 3 ∣ (125 : 𝓞 K5) := by
  have : (125 : 𝓞 K5) = (lam ^ 4 * u5) ^ 3 := by rw [five_eq]; norm_num
  rw [this]; exact ⟨lam ^ 9 * u5 ^ 3, by ring⟩

/-- The second stage: from `ρ⁵ + (σρ)⁵ = E' 2^j W⁵` to a smaller real solution. -/
theorem stageP {j : ℕ} (hj : j = 1 ∨ j = 3) {ρ W : 𝓞 K5} {c : ℤ} {E' : (𝓞 K5)ˣ}
    (hρc : lam ^ 2 ∣ ρ - c) (hρ3 : (2 : 𝓞 K5) ∣ ρ ^ 3 - 1) (hcop : IsCoprime ρ (σ ρ))
    (hlW : ¬ lam ∣ W) (heq : ρ ^ 5 + (σ ρ) ^ 5 = E' * 2 ^ j * W ^ 5) :
    ∃ X' Y' Z' : 𝓞 K5, ∃ E'' : (𝓞 K5)ˣ, σ X' = X' ∧ σ Y' = Y' ∧ IsCoprime X' Y' ∧
      ¬ lam ∣ X' ∧ ¬ lam ∣ Y' ∧ ¬ lam ∣ Z' ∧ X' ^ 5 + Y' ^ 5 = E'' * 2 ^ j * Z' ^ 5 ∧
      Ideal.absNorm (Ideal.span {Z'}) ≤ Ideal.absNorm (Ideal.span {W}) ∧
      (IsUnit (X' + ζ * Y') → IsUnit ρ) := by
  set y := σ ρ with hy
  have hσy : σ y = ρ := σσ ρ
  have hz5 := ζ_pow_five
  -- `2 ∣ ρ + σρ`
  have h2d : (2 : 𝓞 K5) ∣ ρ - y := by
    have h4 := frob4 ρ
    have : ρ - y = (ρ ^ 4 - y) - ρ * (ρ ^ 3 - 1) := by ring
    rw [this]; exact dvd_sub h4 (dvd_mul_of_dvd_right hρ3 _)
  have h2B0 : (2 : 𝓞 K5) ∣ ρ + y := by
    have := dvd_add h2d (dvd_mul_right 2 y); convert this using 1; ring
  have hlB0 : ¬ lam ∣ ρ + y := not_lam_sum hlW heq
  have hcopall := all_coprime hcop hlB0
  have hodd : ∀ i, 1 ≤ i → i < 5 → ¬ (2 : 𝓞 K5) ∣ ρ + ζ ^ i * y := by
    intro i hi1 hi h
    obtain ⟨w, hw, hw'⟩ := one_sub_pow_eq i (by omega)
    have : (2 : 𝓞 K5) ∣ lam * (-w) * y := by
      have := dvd_sub h h2B0
      convert this using 1; linear_combination y * hw'
    have h2y := two_not_dvd_lam_mul hw.neg this
    have h2ρ : (2 : 𝓞 K5) ∣ ρ := by
      have := dvd_sub h2B0 h2y; simpa using this
    exact two_prime.not_unit (hcop.isUnit_of_dvd' h2ρ h2y)
  have hW0 : W ≠ 0 := fun h => hlW (h ▸ dvd_zero _)
  obtain ⟨e0, e1, e2, e3, e4, S0, s1, s2, s3, s4, hB0, hB1, hB2, hB3, hB4, hass⟩ :=
    five_factor hW0 hcopall hodd heq
  -- realify `ζ² B₁` and `ζ³ B₄`
  have hσ1 : σ (ζ ^ 2 * (ρ + ζ * y)) = ζ ^ 2 * (ρ + ζ * y) := by
    rw [map_mul, map_add, map_mul, σ_zeta_pow, σ_ζ, hσy]
    linear_combination (ζ ^ 3 * y + ρ * ζ ^ 2 * (ζ ^ 5 + 1)) * hz5
  have hσ4 : σ (ζ ^ 3 * (ρ + ζ ^ 4 * y)) = ζ ^ 3 * (ρ + ζ ^ 4 * y) := by
    rw [map_mul, map_add, map_mul, σ_zeta_pow, σ_zeta_pow, hσy]
    linear_combination (ζ ^ 7 * y + ρ * ζ ^ 3 * (ζ ^ 20 + ζ ^ 15 + ζ ^ 10 + ζ ^ 5 + 1)) * hz5
  have hlB : ∀ i, ¬ lam ∣ ρ + ζ ^ i * y := lam_factor hlB0
  have hzu : ∀ k : ℕ, ((ζu ^ k : (𝓞 K5)ˣ) : 𝓞 K5) = ζ ^ k := by
    intro k; rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  have hw1 : ζ ^ 2 * (ρ + ζ * y) = ((ζu ^ 2 * e1 : (𝓞 K5)ˣ) : 𝓞 K5) * s1 ^ 5 := by
    rw [Units.val_mul, hzu, hB1]; ring
  have hw4 : ζ ^ 3 * (ρ + ζ ^ 4 * y) = ((ζu ^ 3 * e4 : (𝓞 K5)ˣ) : 𝓞 K5) * s4 ^ 5 := by
    rw [Units.val_mul, hzu, hB4]; ring
  have hB1ne : ζ ^ 2 * (ρ + ζ * y) ≠ 0 := by
    intro h; apply hlB 1; rw [pow_one]
    have : ρ + ζ * y = 0 := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ ζ_ne_zero)
    rw [this]; exact dvd_zero _
  have hB4ne : ζ ^ 3 * (ρ + ζ ^ 4 * y) ≠ 0 := by
    intro h; apply hlB 4
    have : ρ + ζ ^ 4 * y = 0 := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ ζ_ne_zero)
    rw [this]; exact dvd_zero _
  obtain ⟨hu1σ, R1, hR1σ, hR1⟩ := realify hσ1 hB1ne hw1
  obtain ⟨hu4σ, R4, hR4σ, hR4⟩ := realify hσ4 hB4ne hw4
  generalize ζu ^ 2 * e1 = u1 at hu1σ hR1
  generalize ζu ^ 3 * e4 = u4 at hu4σ hR4
  -- Kummer step
  have hρy : lam ^ 2 ∣ ρ - y := by
    have := dvd_sub hρc (lam2_conj hρc); convert this using 1; ring
  have hk3 : lam ^ 3 ∣ (u4 : 𝓞 K5) * R4 ^ 5 - u1 * R1 ^ 5 := by
    obtain ⟨t, ht⟩ := hρy
    refine ⟨-ζ ^ 2 * t, ?_⟩
    rw [← hR4, ← hR1]
    linear_combination (ζ ^ 2 * y) * hz5 - (ζ ^ 2 * lam) * ht
  obtain ⟨d1, hd1⟩ := exists_int_congr R1
  obtain ⟨d4, hd4⟩ := exists_int_congr R4
  have hk3' : lam ^ 3 ∣ (u4 : 𝓞 K5) * (d4 : 𝓞 K5) ^ 5 - u1 * (d1 : 𝓞 K5) ^ 5 := by
    have e1' := dvd_trans (pow_dvd_pow lam (by norm_num : 3 ≤ 5)) (pow_five_congr hd1)
    have e4' := dvd_trans (pow_dvd_pow lam (by norm_num : 3 ≤ 5)) (pow_five_congr hd4)
    have := dvd_add (dvd_sub hk3 (dvd_mul_of_dvd_right e4' (u4 : 𝓞 K5)))
      (dvd_mul_of_dvd_right e1' (u1 : 𝓞 K5))
    convert this using 1; ring
  obtain ⟨δ, hδ⟩ : ∃ δ : (𝓞 K5)ˣ, δ = u4 * u1⁻¹ := ⟨_, rfl⟩
  have hδd : lam ^ 3 ∣ (δ : 𝓞 K5) * (d4 : 𝓞 K5) ^ 5 - (d1 : 𝓞 K5) ^ 5 := by
    have := dvd_mul_of_dvd_right hk3' ((u1⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)
    convert this using 1
    rw [hδ, Units.val_mul]
    have : ((u1⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) * u1 = 1 := Units.inv_mul _
    linear_combination ((d1 : 𝓞 K5) ^ 5) * this
  have hlR4 : ¬ lam ∣ R4 := by
    intro h; apply hlB 4
    have : lam ∣ ζ ^ 3 * (ρ + ζ ^ 4 * y) := by
      rw [hR4]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _
    exact lam_dvd_mul_unit ((ζ_prim.isUnit (by norm_num)).pow 3) this
  have hlR1 : ¬ lam ∣ R1 := by
    intro h; apply hlB 1; rw [pow_one]
    have : lam ∣ ζ ^ 2 * (ρ + ζ * y) := by
      rw [hR1]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _
    exact lam_dvd_mul_unit ((ζ_prim.isUnit (by norm_num)).pow 2) this
  have h5d4 : ¬ (5 : ℤ) ∣ d4 := by
    intro h5; apply hlR4
    have := dvd_add hd4 (by simpa using lam_pow_dvd_of_five_dvd h5 (j := 1) (by norm_num))
    simpa using this
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  obtain ⟨xx, zz, hxz⟩ : IsCoprime (d4 ^ 5) ((5 : ℤ) ^ 3) :=
    (((Prime.coprime_iff_not_dvd hp5).mpr h5d4).symm.pow)
  have hxz' : (xx : 𝓞 K5) * (d4 : 𝓞 K5) ^ 5 + (zz : 𝓞 K5) * 125 = 1 := by
    have := congrArg (fun t : ℤ => (t : 𝓞 K5)) hxz; push_cast at this; linear_combination this
  have hδm : lam ^ 3 ∣ (δ : 𝓞 K5) - ((xx * d1 ^ 5 : ℤ) : 𝓞 K5) := by
    have := dvd_add (dvd_mul_of_dvd_right hδd (xx : 𝓞 K5))
      (dvd_mul_of_dvd_right lam3_dvd_125 ((δ : 𝓞 K5) * zz))
    convert this using 1; push_cast; linear_combination (-(δ : 𝓞 K5)) * hxz'
  obtain ⟨η, hη⟩ := kummer_lemma δ _ hδm
  have hδσ : σ (δ : 𝓞 K5) = δ := by
    rw [hδ, Units.val_mul, map_mul, hu4σ, σ_unit_inv hu1σ]
  obtain ⟨-, R, hRσ, hRδ⟩ := realify (e := 1) (t := (η : 𝓞 K5)) hδσ δ.ne_zero
    (by rw [hη, Units.val_one, one_mul, Units.val_pow_eq_pow_val])
  rw [Units.val_one, one_mul] at hRδ
  -- the new equation
  have hRu : IsUnit R := by
    have : IsUnit (R ^ 5) := by rw [← hRδ]; exact δ.isUnit
    exact (isUnit_pow_iff (by norm_num)).mp this
  have hsum0 : ζ ^ 2 * (ζ - 1) * ((u1 : 𝓞 K5) * R1 ^ 5 + (u4 : 𝓞 K5) * R4 ^ 5
      + φ * (2 ^ j * e0 * S0 ^ 5)) = 0 := by
    rw [← hR1, ← hR4, ← hB0]
    linear_combination (y * ζ ^ 5 - y * ζ ^ 4 + ζ ^ 2 * (ρ + y)) * hz5
  have hz1 : ζ ^ 2 * (ζ - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ ζ_ne_zero)
    (sub_ne_zero.mpr ζ_ne_one)
  have hsum : (u1 : 𝓞 K5) * R1 ^ 5 + (u4 : 𝓞 K5) * R4 ^ 5 = -(φ * (2 ^ j * e0 * S0 ^ 5)) := by
    have := (mul_eq_zero.mp hsum0).resolve_left hz1; linear_combination this
  have hu4 : (u4 : 𝓞 K5) = u1 * R ^ 5 := by
    rw [← hRδ, hδ, Units.val_mul]
    have : ((u1⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) * u1 = 1 := Units.inv_mul _
    linear_combination (-(u4 : 𝓞 K5)) * this
  have hΦ : ((Φ : (𝓞 K5)ˣ) : 𝓞 K5) = φ := IsUnit.unit_spec _
  have hE'' : (((-(Φ * u1⁻¹ * e0)) : (𝓞 K5)ˣ) : 𝓞 K5) = -(φ * ((u1⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) * e0) := by
    rw [Units.val_neg, Units.val_mul, Units.val_mul, hΦ]
  have hnew : R1 ^ 5 + (R * R4) ^ 5 = (-(Φ * u1⁻¹ * e0) : (𝓞 K5)ˣ) * 2 ^ j * S0 ^ 5 := by
    apply mul_left_cancel₀ u1.ne_zero
    have hinv : (u1 : 𝓞 K5) * ((u1⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = 1 := Units.mul_inv _
    rw [hE'']
    linear_combination hsum - (R4 ^ 5) * hu4 + (φ * 2 ^ j * e0 * S0 ^ 5) * hinv
  -- properties of the new solution
  have hR1d : R1 ∣ ρ + ζ * y :=
    ⟨ζ ^ 3 * u1 * R1 ^ 4, by linear_combination ζ ^ 3 * hR1 - (ρ + ζ * y) * hz5⟩
  have hR4d : R4 ∣ ρ + ζ ^ 4 * y :=
    ⟨ζ ^ 2 * u4 * R4 ^ 4, by linear_combination ζ ^ 2 * hR4 - (ρ + ζ ^ 4 * y) * hz5⟩
  have c14 : IsCoprime (ρ + ζ * y) (ρ + ζ ^ 4 * y) := by
    simpa using hcopall 1 4 (by norm_num) (by norm_num)
  have hcR : IsCoprime R1 (R * R4) :=
    (isCoprime_mul_unit_left_right hRu R1 R4).mpr
      ((c14.of_isCoprime_of_dvd_left hR1d).of_isCoprime_of_dvd_right hR4d)
  have hlRR4 : ¬ lam ∣ R * R4 := by
    intro h; exact hlR4 (lam_dvd_mul_unit hRu h)
  have hS0W : S0 ∣ W := dvd_trans ⟨s1 * s2 * s3 * s4, by ring⟩ hass.dvd
  have hlS0 : ¬ lam ∣ S0 := fun h => hlW (dvd_trans h hS0W)
  have hRR4σ : σ (R * R4) = R * R4 := by rw [map_mul, hRσ, hR4σ]
  refine ⟨R1, R * R4, S0, -(Φ * u1⁻¹ * e0), hR1σ, hRR4σ, hcR, hlR1, hlRR4, hlS0, hnew, ?_, ?_⟩
  · -- norm bound
    rw [← absNorm_assoc hass, absNorm_mul', absNorm_mul', absNorm_mul', absNorm_mul']
    have hne : ∀ t : 𝓞 K5, t ∣ W → t ≠ 0 := fun t ht h0 => hW0 (by rw [h0] at ht; exact zero_dvd_iff.mp ht)
    have hd : ∀ t, t ∣ S0 * s1 * s2 * s3 * s4 → t ∣ W := fun t ht => dvd_trans ht hass.dvd
    have p1 := absNorm_pos (hne s1 (hd s1 ⟨S0 * s2 * s3 * s4, by ring⟩))
    have p2 := absNorm_pos (hne s2 (hd s2 ⟨S0 * s1 * s3 * s4, by ring⟩))
    have p3 := absNorm_pos (hne s3 (hd s3 ⟨S0 * s1 * s2 * s4, by ring⟩))
    have p4 := absNorm_pos (hne s4 (hd s4 ⟨S0 * s1 * s2 * s3, by ring⟩))
    calc Ideal.absNorm (Ideal.span {S0}) = Ideal.absNorm (Ideal.span {S0}) * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  · -- backward
    intro hU
    obtain ⟨kf', -⟩ := stageR hR1σ hRR4σ hcR hlR1 hlRR4 hlS0 hnew
    obtain ⟨a, wv, hv, hwv⟩ := unit_decomp' hU.unit
    rw [IsUnit.unit_spec] at hv
    have ha := kf' a wv 1 hwv (by rw [one_pow, mul_one]; exact hv)
    have hza : ζ ^ a = ζ ^ 3 := ζ_pow_eq_of_mod (by omega)
    rw [hza] at hv
    have hXY := eq_of_unit_form hR1σ hRR4σ hwv hv
    have hR1u : IsUnit R1 := isCoprime_self.mp (by rw [← hXY] at hcR; exact hcR)
    have hR15 : IsUnit (R1 ^ 5) := hR1u.pow 5
    have hj1 : j = 1 := by
      rcases hj with h | h
      · exact h
      · exfalso; subst h
        rw [← hXY] at hnew
        have h2 : (2 : 𝓞 K5) ∣ R1 ^ 5 := by
          refine ⟨2 * (((-(Φ * u1⁻¹ * e0)) : (𝓞 K5)ˣ) : 𝓞 K5) * S0 ^ 5, ?_⟩
          apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 K5) ≠ 0)
          linear_combination hnew
        exact two_prime.not_unit (isUnit_of_dvd_unit h2 hR15)
    subst hj1
    rw [← hXY] at hnew
    have hS0u : IsUnit S0 := by
      have : R1 ^ 5 = (((-(Φ * u1⁻¹ * e0)) : (𝓞 K5)ˣ) : 𝓞 K5) * S0 ^ 5 :=
        mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 K5) ≠ 0) (by linear_combination hnew)
      rw [this] at hR15
      exact (isUnit_pow_iff (by norm_num)).mp (isUnit_of_mul_isUnit_right hR15)
    have hR4u : IsUnit R4 := isUnit_of_mul_isUnit_right (hXY ▸ hR1u)
    -- the unit equation
    set U1 := (u1 : 𝓞 K5) * R1 ^ 5 with hU1
    set U4 := (u4 : 𝓞 K5) * R4 ^ 5 with hU4
    set U0 := (e0 : 𝓞 K5) * S0 ^ 5 with hU0
    have hU0u : IsUnit U0 := e0.isUnit.mul (hS0u.pow 5)
    have hU1u : IsUnit U1 := u1.isUnit.mul (hR1u.pow 5)
    have hU4u : IsUnit U4 := u4.isUnit.mul (hR4u.pow 5)
    have hsum1 : U1 + U4 = -(φ * (2 * U0)) := by rw [hsum]; ring
    have hB1' : ρ + ζ * y = ζ ^ 3 * U1 := by linear_combination ζ ^ 3 * hR1 - (ρ + ζ * y) * hz5
    have hB0' : ρ + y = 2 * U0 := by rw [hB0]; ring
    have hU0σ : σ U0 = U0 := by
      have h1 : σ (ρ + y) = ρ + y := by rw [map_add, hσy]; ring
      rw [hB0'] at h1; rw [map_mul, map_ofNat] at h1
      exact mul_left_cancel₀ two_ne_zero h1
    have hU1σ : σ U1 = U1 := by rw [hU1, map_mul, hu1σ, map_pow, hR1σ]
    set P : (𝓞 K5)ˣ := Φ * hU0u.unit with hP
    have hPv : (P : 𝓞 K5) = φ * U0 := by rw [hP, Units.val_mul, hΦ, IsUnit.unit_spec]
    have hPσ : σ (P : 𝓞 K5) = P := by rw [hPv, map_mul, σ_φ, hU0σ]
    have hinvP : ((P⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) * (φ * U0) = 1 := by rw [← hPv, Units.inv_mul]
    set v := -U1 * ((P⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) with hvdef
    have hvσ : σ v = v := by rw [hvdef, map_mul, map_neg, hU1σ, σ_unit_inv hPσ]
    have hvu : IsUnit v := hU1u.neg.mul P⁻¹.isUnit
    have h2v : IsUnit (2 - v) := by
      have : 2 - v = -U4 * ((P⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) := by
        rw [hvdef]; linear_combination (-(2 : 𝓞 K5)) * hinvP + ((P⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) * hsum1
      rw [this]; exact hU4u.neg.mul P⁻¹.isUnit
    have hkey : lam * ρ = U0 * ((1 + ζ) * v - 2 * ζ) := by
      rw [hvdef]
      linear_combination hB1' - ζ * hB0' - ζ ^ 3 * U1 * hinvP
        + (U1 * U0 * ((P⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) * cyc
        + (ζ ^ 2 * U1 * U0 * ((P⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5)) * hz5
    have hlv : lam ∣ v - 1 := by
      have h1 : lam ∣ U0 * ((1 + ζ) * v - 2 * ζ) := ⟨ρ, hkey.symm⟩
      have h2 := lam_dvd_mul_unit hU0u h1
      have h3 : lam ∣ 2 * (v - 1) := by
        have := dvd_add h2 (dvd_mul_of_dvd_left (dvd_refl lam) (v - 2))
        convert this using 1; ring
      rcases lam_prime.dvd_or_dvd h3 with h | h
      · exact absurd h lam_not_dvd_two
      · exact h
    have hv1 := unit_eq_two hvσ hvu h2v hlv
    have hρU : ρ = U0 := by
      apply mul_left_cancel₀ lam_ne_zero
      rw [hkey, hv1]; ring
    rw [hρU]; exact hU0u


end StageP

section Descent

/-- **The descent** (case a): every real solution has `X + ζ Y` a unit. -/
theorem descent (n : ℕ) : ∀ (j : ℕ), (j = 1 ∨ j = 3) → ∀ (X Y Z : 𝓞 K5) (E : (𝓞 K5)ˣ),
    σ X = X → σ Y = Y → IsCoprime X Y → ¬ lam ∣ X → ¬ lam ∣ Y → ¬ lam ∣ Z →
    X ^ 5 + Y ^ 5 = E * 2 ^ j * Z ^ 5 → Ideal.absNorm (Ideal.span {Z}) = n →
    IsUnit (X + ζ * Y) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hj X Y Z E hX hY hcop hlX hlY hlZ heq hn
  by_contra hnu
  obtain ⟨-, r1, r2, r0, t1, t2, W, hr1, hr2, hr0, hWσ, h1, h2, h0, hnorm⟩ :=
    stageR hX hY hcop hlX hlY hlZ heq
  have hlXY := not_lam_sum hlZ heq
  have hgood := good_t1 hj hX hY hcop hlXY hr2 hr0 h1 h2 h0
  have hlt1 : ¬ lam ∣ t1 := by
    intro h; apply lam_factor hlXY 1; rw [pow_one, h1]
    exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _
  obtain ⟨k, c, hkc⟩ := normalize hlt1
  have hρ3 := hgood k c hkc
  have hz5 := ζ_pow_five
  have hρ5 : (ζ ^ k * t1) ^ 5 = t1 ^ 5 := by
    rw [mul_pow, ← pow_mul, show k * 5 = 5 * k by ring, pow_mul, hz5, one_pow, one_mul]
  have hσ1 : σ (X + ζ * Y) = X + ζ ^ 4 * Y := by rw [map_add, map_mul, hX, hY, σ_ζ]
  have hA : X + ζ * Y = ζ ^ 3 * r1 * (ζ ^ k * t1) ^ 5 := by rw [hρ5, h1]
  have hB : X + ζ ^ 4 * Y = ζ ^ 2 * r1 * (σ (ζ ^ k * t1)) ^ 5 := by
    rw [← hσ1, hA, σ_pow_conj hr1, show ζ ^ (4 * 3) = ζ ^ 2 from ζ_pow_eq_of_mod (by norm_num)]
  set ρ := ζ ^ k * t1 with hρ
  have c14 : IsCoprime (X + ζ * Y) (X + ζ ^ 4 * Y) := by
    simpa using all_coprime hcop hlXY 1 4 (by norm_num) (by norm_num)
  have hcopρ : IsCoprime ρ (σ ρ) := by
    rw [hA, hB] at c14
    exact (c14.of_isCoprime_of_dvd_left ⟨ζ ^ 3 * r1 * ρ ^ 4, by ring⟩).of_isCoprime_of_dvd_right
      ⟨ζ ^ 2 * r1 * (σ ρ) ^ 4, by ring⟩
  have hz1 : ζ ^ 2 * (ζ - 1) ≠ 0 := mul_ne_zero (pow_ne_zero _ ζ_ne_zero)
    (sub_ne_zero.mpr ζ_ne_one)
  have hsum0 : ζ ^ 2 * (ζ - 1) * ((r1 : 𝓞 K5) * (ρ ^ 5 + (σ ρ) ^ 5) + φ * (2 ^ j * r0 * W ^ 5)) = 0 := by
    rw [← h0]
    have eA : (r1 : 𝓞 K5) * ρ ^ 5 = ζ ^ 2 * (X + ζ * Y) := by rw [hA]; linear_combination (-(r1 : 𝓞 K5) * ρ ^ 5) * hz5
    have eB : (r1 : 𝓞 K5) * (σ ρ) ^ 5 = ζ ^ 3 * (X + ζ ^ 4 * Y) := by
      rw [hB]; linear_combination (-(r1 : 𝓞 K5) * (σ ρ) ^ 5) * hz5
    rw [mul_add (r1 : 𝓞 K5), eA, eB]
    linear_combination (Y * ζ ^ 5 - Y * ζ ^ 4 + ζ ^ 2 * (X + Y)) * hz5
  have hsum : (r1 : 𝓞 K5) * (ρ ^ 5 + (σ ρ) ^ 5) = -(φ * (2 ^ j * r0 * W ^ 5)) := by
    have := (mul_eq_zero.mp hsum0).resolve_left hz1; linear_combination this
  have hΦ : ((Φ : (𝓞 K5)ˣ) : 𝓞 K5) = φ := IsUnit.unit_spec _
  have heqρ : ρ ^ 5 + (σ ρ) ^ 5 = ((-(Φ * r1⁻¹ * r0)) : (𝓞 K5)ˣ) * 2 ^ j * W ^ 5 := by
    apply mul_left_cancel₀ r1.ne_zero
    have hinv : (r1 : 𝓞 K5) * ((r1⁻¹ : (𝓞 K5)ˣ) : 𝓞 K5) = 1 := Units.mul_inv _
    rw [Units.val_neg, Units.val_mul, Units.val_mul, hΦ]
    linear_combination hsum + (φ * 2 ^ j * r0 * W ^ 5) * hinv
  have hlW : ¬ lam ∣ W := by
    intro h; apply hlXY; rw [h0]; exact dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _
  obtain ⟨X', Y', Z', E'', hX', hY', hcop', hlX', hlY', hlZ', heq', hZ'W, hback⟩ :=
    stageP hj hkc hρ3 hcopρ hlW heqρ
  have ht1nu : ¬ IsUnit t1 := by
    intro hu; apply hnu; rw [h1]
    exact (((ζ_prim.isUnit (by norm_num)).pow 3).mul r1.isUnit).mul (hu.pow 5)
  have hWpos : 0 < Ideal.absNorm (Ideal.span {W}) := absNorm_pos (fun h => hlW (h ▸ dvd_zero _))
  have ht1 : 2 ≤ Ideal.absNorm (Ideal.span {t1}) := by
    have h0' := absNorm_pos (a := t1) (fun h => hlt1 (h ▸ dvd_zero _))
    have h1' : Ideal.absNorm (Ideal.span {t1}) ≠ 1 := fun h => ht1nu (absNorm_eq_one.mp h)
    omega
  have hlt : Ideal.absNorm (Ideal.span {Z'}) < n := by
    rw [← hn]; nlinarith
  have hU := ih _ hlt j hj X' Y' Z' E'' hX' hY' hcop' hlX' hlY' hlZ' heq' rfl
  have hρu := hback hU
  apply ht1nu
  have : IsUnit (ζ ^ k * t1) := hρu
  exact isUnit_of_mul_isUnit_right this

/-- **Dénes, case a**: `x⁵ + y⁵ = 2^j z⁵` (`j = 1, 3`) with `5 ∤ xyz`, `x, y` coprime, forces
`x = y` and `j = 1`. -/
theorem case_a {x y z : ℤ} {j : ℕ} (hj : j = 1 ∨ j = 3) (h : x ^ 5 + y ^ 5 = 2 ^ j * z ^ 5)
    (hxy : IsCoprime x y) (hx : ¬ (5 : ℤ) ∣ x) (hy : ¬ (5 : ℤ) ∣ y) (hz : ¬ (5 : ℤ) ∣ z) :
    x = y ∧ j = 1 := by
  have hX : σ (x : 𝓞 K5) = x := map_intCast σ x
  have hY : σ (y : 𝓞 K5) = y := map_intCast σ y
  have hcop : IsCoprime (x : 𝓞 K5) (y : 𝓞 K5) := hxy.map (Int.castRingHom (𝓞 K5))
  have hlX : ¬ lam ∣ (x : 𝓞 K5) := fun hl => hx (lam_dvd_int hl)
  have hlY : ¬ lam ∣ (y : 𝓞 K5) := fun hl => hy (lam_dvd_int hl)
  have hlZ : ¬ lam ∣ (z : 𝓞 K5) := fun hl => hz (lam_dvd_int hl)
  have heq : (x : 𝓞 K5) ^ 5 + (y : 𝓞 K5) ^ 5 = ((1 : (𝓞 K5)ˣ) : 𝓞 K5) * 2 ^ j * (z : 𝓞 K5) ^ 5 := by
    have := congrArg (fun t : ℤ => (t : 𝓞 K5)) h; push_cast at this; rw [this]; simp
  have hU := descent _ j hj _ _ _ 1 hX hY hcop hlX hlY hlZ heq rfl
  obtain ⟨kf, -⟩ := stageR hX hY hcop hlX hlY hlZ heq
  obtain ⟨a, w, hv, hw⟩ := unit_decomp' hU.unit
  rw [IsUnit.unit_spec] at hv
  have ha := kf a w 1 hw (by rw [one_pow, mul_one]; exact hv)
  rw [show ζ ^ a = ζ ^ 3 from ζ_pow_eq_of_mod (by omega)] at hv
  have hxyO := eq_of_unit_form hX hY hw hv
  have hxy' : x = y := Int.cast_injective hxyO
  refine ⟨hxy', ?_⟩
  subst hxy'
  rcases hj with rfl | rfl
  · rfl
  · exfalso
    have hu : IsUnit x := isCoprime_self.mp hxy
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;>
    · have := h; set w := z ^ 5; omega

end Descent

end OMA672Z5


-- ===== CaseA5.lean =====

namespace OMA672Z5

lemma unit_of_pow_dvd {g z : ℤ} {j : ℕ} (hj : j ≤ 3) (hc : IsCoprime g z) (h : g ^ 5 ∣ 2 ^ j * z ^ 5) :
    IsUnit g := by
  have h1 : g ^ 5 ∣ 2 ^ j := (hc.pow (m := 5) (n := 5)).dvd_of_dvd_mul_right h
  have h2 : g ^ 5 ∣ 8 := dvd_trans h1 (pow_dvd_pow 2 hj)
  have hg0 : g ≠ 0 := by rintro rfl; norm_num at h2
  have h3 : (g ^ 5).natAbs ≤ 8 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr h2)
  rw [Int.natAbs_pow] at h3
  have h4 : g.natAbs ≤ 1 := by
    by_contra hh; push_neg at hh
    have : 2 ^ 5 ≤ g.natAbs ^ 5 := Nat.pow_le_pow_left hh 5
    omega
  rw [Int.isUnit_iff_natAbs_eq]; have := Int.natAbs_pos.mpr hg0; omega

/-- Coprime form of Dénes (`l = 5`, `A = 2^j`, `j = 1, 3`). -/
theorem denes_coprime {x y z : ℤ} {j : ℕ} (hj : j = 1 ∨ j = 3) (h : x ^ 5 + y ^ 5 = 2 ^ j * z ^ 5)
    (hxy : IsCoprime x y) : z = 0 ∨ (x = y ∧ j = 1) := by
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  right
  have hj1 : 1 ≤ j := by omega
  by_cases hz5 : (5 : ℤ) ∣ z
  · exact (case_c h hxy hz5 hz0).elim
  by_cases hy5 : (5 : ℤ) ∣ y
  · exact (case_b hj1 h hxy hy5).elim
  by_cases hx5 : (5 : ℤ) ∣ x
  · exact (case_b (x := y) (y := x) (z := z) hj1 (by linear_combination h) hxy.symm hx5).elim
  exact case_a hj h hxy hx5 hy5 hz5

/-- **Dénes' theorem for `l = 5`** with `A = 2` or `8`, all integers. -/
theorem denes {x y z : ℤ} {j : ℕ} (hj : j = 1 ∨ j = 3) (h : x ^ 5 + y ^ 5 = 2 ^ j * z ^ 5) :
    z = 0 ∨ (x = y ∧ j = 1) := by
  by_cases hxy0 : x = 0 ∧ y = 0
  · left; obtain ⟨rfl, rfl⟩ := hxy0
    have : (2 : ℤ) ^ j * z ^ 5 = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (pow_ne_zero _ (by norm_num))
    · exact pow_eq_zero_iff (by norm_num) |>.mp h'
  have hpos : 0 < Int.gcd x y := by
    rcases not_and_or.mp hxy0 with hx | hy
    · exact Int.gcd_pos_of_ne_zero_left _ hx
    · exact Int.gcd_pos_of_ne_zero_right _ hy
  obtain ⟨g, x', y', hg, hgcd, rfl, rfl⟩ := Int.exists_gcd_one' hpos
  have hcop : IsCoprime x' y' := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  obtain ⟨d, g', z', hd, hdgcd, hgd, hzd⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_right (g : ℤ) hz0)
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have heq' : g' ^ 5 * (x' ^ 5 + y' ^ 5) = 2 ^ j * z' ^ 5 := by
    apply mul_left_cancel₀ (pow_ne_zero 5 hd0)
    have : ((g : ℤ)) ^ 5 * (x' ^ 5 + y' ^ 5) = 2 ^ j * z ^ 5 := by linear_combination h
    rw [hgd, hzd] at this; linear_combination this
  have hg'u : IsUnit g' := unit_of_pow_dvd (by omega) (Int.isCoprime_iff_gcd_eq_one.mpr hdgcd)
    ⟨x' ^ 5 + y' ^ 5, heq'.symm⟩
  rcases Int.isUnit_iff.mp hg'u with h1 | h1 <;> rw [h1] at heq'
  · rcases denes_coprime hj (x := x') (y := y') (z := z') (by linear_combination heq') hcop with h2 | ⟨h2, h3⟩
    · left; rw [hzd, h2, zero_mul]
    · right; exact ⟨by rw [h2], h3⟩
  · rcases denes_coprime hj (x := -x') (y := -y') (z := z') (by linear_combination heq')
      hcop.neg_left.neg_right with h2 | ⟨h2, h3⟩
    · left; rw [hzd, h2, zero_mul]
    · right; exact ⟨by rw [neg_inj.mp h2], h3⟩

theorem H1 : ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 2 * z ^ 5 → x = y ∨ z = 0 := by
  intro x y z h
  rcases denes (j := 1) (Or.inl rfl) (by simpa using h) with h | h
  · exact Or.inr h
  · exact Or.inl h.1

theorem H2 : ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 8 * z ^ 5 → z = 0 := by
  intro x y z h
  rcases denes (j := 3) (Or.inr rfl) (by norm_num; exact h) with h | h
  · exact h
  · exact absurd h.2 (by norm_num)

end OMA672Z5

namespace OMA672H4

/-- Denes (p = 5): `x ^ 5 + y ^ 5 = 2 z ^ 5` forces `x = y` or `z = 0`. -/
def H1 : Prop := ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 2 * z ^ 5 → x = y ∨ z = 0

/-- Ribet (p = 5, k = 3): `x ^ 5 + y ^ 5 = 8 z ^ 5` forces `z = 0`. -/
def H2 : Prop := ∀ x y z : ℤ, x ^ 5 + y ^ 5 = 8 * z ^ 5 → z = 0

lemma fifth_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (habc : a * b = c ^ 5) :
    ∃ u, a = u ^ 5 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) habc

lemma split_even5 {E O m : ℕ} (hc : Nat.Coprime E O) (hO : Odd O) (h : E * O = 8 * m ^ 5) :
    ∃ u w, E = 8 * u ^ 5 ∧ O = w ^ 5 := by
  have hO2 : Nat.Coprime 2 O := (Nat.coprime_two_left).mpr hO
  have step : ∀ F k : ℕ, F * O = 2 * k → ∃ F', F = 2 * F' := by
    intro F k hF
    have : 2 ∣ F * O := ⟨k, hF⟩
    exact hO2.dvd_of_dvd_mul_right this
  obtain ⟨E1, rfl⟩ := step E (4 * m ^ 5) (by rw [h]; ring)
  obtain ⟨E2, rfl⟩ := step E1 (2 * m ^ 5) (by nlinarith [h])
  obtain ⟨E3, rfl⟩ := step E2 (m ^ 5) (by nlinarith [h])
  have h3 : E3 * O = m ^ 5 := by nlinarith [h]
  have hc3 : Nat.Coprime E3 O := by
    have : E3 ∣ 2 * (2 * (2 * E3)) := ⟨8, by ring⟩
    exact Nat.Coprime.coprime_dvd_left this hc
  obtain ⟨u, hu⟩ := fifth_of_coprime hc3 h3
  obtain ⟨w, hw⟩ := fifth_of_coprime hc3.symm (by rw [mul_comm]; exact h3)
  exact ⟨u, w, by rw [hu]; ring, hw⟩

theorem ap3_ne_fifth (den : H1) (rib : H2) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) : n * ((n + d) * (n + 2 * d)) ≠ q ^ 5 := by
  intro hq
  have c1 : Nat.Coprime (n + d) n := by
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.Coprime.symm hnd
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := by
    have : n + 2 * d = (n + d) + d := by ring
    rw [this, Nat.coprime_self_add_right, Nat.coprime_add_self_left]; exact hnd
  have hmid : (n + d) * (n * (n + 2 * d)) = q ^ 5 := by rw [← hq]; ring
  obtain ⟨b, hb⟩ := fifth_of_coprime (Nat.Coprime.mul_right c1 c2) hmid
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb; omega
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨A, hA⟩ := hev
    have hA' : n = 2 * A := by omega
    subst hA'
    have hdodd : Odd d := by
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | h
      · exfalso
        have : 2 ∣ Nat.gcd (2 * A) d := Nat.dvd_gcd ⟨A, rfl⟩ ⟨k, by omega⟩
        rw [hnd] at this; omega
      · exact h
    have hcAC : Nat.Coprime A (A + d) := by
      rw [Nat.coprime_self_add_right]; exact Nat.Coprime.coprime_mul_left hnd
    have hBA : (2 * A * (2 * A + 2 * d)) * (2 * A + d) = q ^ 5 := by rw [← hmid]; ring
    obtain ⟨m, hm⟩ := fifth_of_coprime (Nat.Coprime.mul_right c1 c2).symm hBA
    have hm2 : 2 ∣ m := by
      have : 2 ∣ m ^ 5 := ⟨2 * A * (A + d), by rw [← hm]; ring⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    obtain ⟨m', rfl⟩ := hm2
    have hAC : A * (A + d) = 8 * m' ^ 5 := by nlinarith [hm]
    have hsum : 2 * A + d = A + (A + d) := by ring
    have hApos : 0 < A := by omega
    have key : ∀ E O : ℕ, Nat.Coprime E O → Odd O → E * O = 8 * m' ^ 5 → E + O = b ^ 5 →
        0 < E → False := by
      intro E O hc hO hEO hsum' hE
      obtain ⟨u, w, hu, hw⟩ := split_even5 hc hO hEO
      have k : (b : ℤ) ^ 5 + (-(w : ℤ)) ^ 5 = 8 * (u : ℤ) ^ 5 := by
        have : b ^ 5 = 8 * u ^ 5 + w ^ 5 := by rw [← hsum', hu, hw]
        have : ((b ^ 5 : ℕ) : ℤ) = ((8 * u ^ 5 + w ^ 5 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      have hu0 : (u : ℤ) = 0 := rib _ _ _ k
      have : u = 0 := by exact_mod_cast hu0
      subst this; simp at hu; omega
    rcases Nat.even_or_odd A with hAe | hAo
    · have hCo : Odd (A + d) := hAe.add_odd hdodd
      exact key A (A + d) hcAC hCo hAC (by rw [← hsum]; exact hb) hApos
    · exact key (A + d) A hcAC.symm hAo (by rw [mul_comm]; exact hAC)
        (by rw [add_comm, ← hsum]; exact hb) (by omega)
  · have c3 : Nat.Coprime n (n + 2 * d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.mul_right hodd.coprime_two_right hnd
    obtain ⟨a, ha⟩ := fifth_of_coprime (Nat.Coprime.mul_right c1.symm c3) hq
    have hlast : (n + 2 * d) * (n * (n + d)) = q ^ 5 := by rw [← hq]; ring
    obtain ⟨c, hc⟩ := fifth_of_coprime (Nat.Coprime.mul_right c3.symm c2.symm) hlast
    have k : (a : ℤ) ^ 5 + (c : ℤ) ^ 5 = 2 * (b : ℤ) ^ 5 := by
      have : a ^ 5 + c ^ 5 = 2 * b ^ 5 := by rw [← ha, ← hb, ← hc]; ring
      exact_mod_cast this
    rcases den _ _ _ k with h | h
    · have : a = c := by exact_mod_cast h
      subst this; omega
    · exact hb0 (by exact_mod_cast h)

end OMA672H4

theorem OMA.solution : OMA.R_Erdos672_erdos_672_variants_oblath_R1.H4 := by
  have den : OMA672H4.H1 := OMA672Z5.H1
  have rib : OMA672H4.H2 := OMA672Z5.H2
  show Erdos672.Erdos672With 3 5
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
  exact OMA672H4.ap3_ne_fifth den rib hn hd hnd hq

