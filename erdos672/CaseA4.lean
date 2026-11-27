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

