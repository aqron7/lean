import CaseA2

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

end OMA672Z5
