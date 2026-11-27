import CaseA4

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
