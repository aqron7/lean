import CaseA3

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

end OMA672Z5
