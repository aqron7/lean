import Mathlib

/-! Erdős 672, Obláth step H2 (3-term AP, cubes), reduced to Euler's theorem on
`x ^ 3 + y ^ 3 = 2 * z ^ 3`. -/

namespace OMA672

/-- Euler: the only integer solutions of `x ^ 3 + y ^ 3 = 2 z ^ 3` have `x = y` or `z = 0`. -/
def EulerCubes : Prop := ∀ x y z : ℤ, x ^ 3 + y ^ 3 = 2 * z ^ 3 → x = y ∨ z = 0

lemma cube_of_coprime {a b c : ℕ} (h : Nat.Coprime a b) (habc : a * b = c ^ 3) : ∃ u, a = u ^ 3 :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr h) habc

/-- If `E * O = 2 * m ^ 3` with `E` even and `E, O` coprime then `E = 2 u ^ 3`, `O = w ^ 3`. -/
lemma split_even {E O m : ℕ} (hc : Nat.Coprime E O) (hE : Even E) (h : E * O = 2 * m ^ 3) :
    ∃ u w, E = 2 * u ^ 3 ∧ O = w ^ 3 := by
  obtain ⟨E', rfl⟩ := hE
  have h' : E' * O = m ^ 3 := by nlinarith [h]
  have hc' : Nat.Coprime E' O := Nat.Coprime.coprime_mul_left (by rwa [← two_mul] at hc)
  obtain ⟨u, hu⟩ := cube_of_coprime hc' h'
  obtain ⟨w, hw⟩ := cube_of_coprime hc'.symm (by rw [mul_comm]; exact h')
  exact ⟨u, w, by rw [hu]; ring, hw⟩

theorem ap3_ne_cube (core : EulerCubes) {n d q : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hnd : n.gcd d = 1) : n * ((n + d) * (n + 2 * d)) ≠ q ^ 3 := by
  intro hq
  have c1 : Nat.Coprime (n + d) n := by
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.Coprime.symm hnd
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := by
    have : n + 2 * d = (n + d) + d := by ring
    rw [this, Nat.coprime_self_add_right, Nat.coprime_add_self_left]; exact hnd
  have hmid : (n + d) * (n * (n + 2 * d)) = q ^ 3 := by rw [← hq]; ring
  obtain ⟨b, hb⟩ := cube_of_coprime (Nat.Coprime.mul_right c1 c2) hmid
  have hb0 : (b : ℤ) ≠ 0 := by
    intro h0; have : b = 0 := by exact_mod_cast h0
    subst this; simp at hb; omega
  rcases Nat.even_or_odd n with hev | hodd
  · -- n even: n = 2A, d odd, A and A + d coprime
    obtain ⟨A, hA⟩ := hev
    have hA' : n = 2 * A := by omega
    subst hA'
    have hdodd : Odd d := by
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | h
      · exfalso
        have : 2 ∣ Nat.gcd (2 * A) d := Nat.dvd_gcd ⟨A, rfl⟩ ⟨k, by omega⟩
        rw [hnd] at this; omega
      · exact h
    have hcAC : Nat.Coprime A (A + d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.coprime_mul_left hnd
    have hrest : 2 * A * (2 * A + 2 * d) = 4 * (A * (A + d)) := by ring
    have hBA : (2 * A * (2 * A + 2 * d)) * (2 * A + d) = q ^ 3 := by rw [← hmid]; ring
    obtain ⟨m, hm⟩ := cube_of_coprime (Nat.Coprime.mul_right c1 c2).symm hBA
    rw [hrest] at hm
    have hm2 : 2 ∣ m := by
      have : 2 ∣ m ^ 3 := ⟨2 * (A * (A + d)), by rw [← hm]; ring⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    obtain ⟨m', rfl⟩ := hm2
    have hAC : A * (A + d) = 2 * m' ^ 3 := by nlinarith [hm]
    have hsum : 2 * A + d = A + (A + d) := by ring
    have hApos : 0 < A := by omega
    rcases Nat.even_or_odd A with hAe | hAo
    · obtain ⟨u, w, hu, hw⟩ := split_even hcAC hAe hAC
      have key : (b : ℤ) ^ 3 + (-(w : ℤ)) ^ 3 = 2 * (u : ℤ) ^ 3 := by
        have : b ^ 3 = 2 * u ^ 3 + w ^ 3 := by rw [← hb, hsum, hw, hu]
        have : ((b ^ 3 : ℕ) : ℤ) = ((2 * u ^ 3 + w ^ 3 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      rcases core _ _ _ key with h | h
      · have hw0 : (0 : ℤ) < w := by
          have : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h0 | h0
            · subst h0; simp at hw; omega
            · exact h0
          exact_mod_cast this
        have : (0 : ℤ) ≤ b := by positivity
        omega
      · have : u = 0 := by exact_mod_cast h
        subst this; simp at hu; omega
    · have hCe : Even (A + d) := by
        rcases hAo with ⟨k, hk⟩; rcases hdodd with ⟨j, hj⟩; exact ⟨k + j + 1, by omega⟩
      obtain ⟨u, w, hu, hw⟩ := split_even hcAC.symm hCe (by rw [mul_comm]; exact hAC)
      have key : (b : ℤ) ^ 3 + (-(w : ℤ)) ^ 3 = 2 * (u : ℤ) ^ 3 := by
        have : b ^ 3 = 2 * u ^ 3 + w ^ 3 := by rw [← hb, hsum, hu, hw]; ring
        have : ((b ^ 3 : ℕ) : ℤ) = ((2 * u ^ 3 + w ^ 3 : ℕ) : ℤ) := by rw [this]
        push_cast at this; linear_combination this
      rcases core _ _ _ key with h | h
      · have hw0 : (0 : ℤ) < w := by
          have : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h0 | h0
            · subst h0; simp at hw; omega
            · exact h0
          exact_mod_cast this
        have : (0 : ℤ) ≤ b := by positivity
        omega
      · have : u = 0 := by exact_mod_cast h
        subst this; simp at hu; omega
  · -- n odd: the three terms are pairwise coprime cubes
    have c3 : Nat.Coprime n (n + 2 * d) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.Coprime.mul_right (hodd.coprime_two_right) hnd
    have hfirst : n * ((n + d) * (n + 2 * d)) = q ^ 3 := hq
    obtain ⟨a, ha⟩ := cube_of_coprime (Nat.Coprime.mul_right c1.symm c3) hfirst
    have hlast : (n + 2 * d) * (n * (n + d)) = q ^ 3 := by rw [← hq]; ring
    obtain ⟨c, hc⟩ := cube_of_coprime (Nat.Coprime.mul_right c3.symm c2.symm) hlast
    have key : (a : ℤ) ^ 3 + (c : ℤ) ^ 3 = 2 * (b : ℤ) ^ 3 := by
      have : a ^ 3 + c ^ 3 = 2 * b ^ 3 := by rw [← ha, ← hb, ← hc]; ring
      exact_mod_cast this
    rcases core _ _ _ key with h | h
    · have : a = c := by exact_mod_cast h
      subst this; omega
    · exact hb0 h

end OMA672
