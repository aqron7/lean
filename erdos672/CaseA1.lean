import Eis2

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

