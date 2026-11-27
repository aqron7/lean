import CaseA1

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
