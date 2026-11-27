import Zeta5

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
