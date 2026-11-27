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

end OMA672Z5
