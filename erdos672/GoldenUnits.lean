import Mathlib

/-! Units of `ℤ[φ]`: if `a² + ac - c² = ±1` then `(a, c)` is reached from `(1, 0)` by repeatedly
multiplying by `φ` or `φ⁻¹ = φ - 1`, where `(a + cφ)·φ = c + (a + c)φ` and
`(a + cφ)(φ - 1) = (c - a) + aφ`. We record this as reachability, which is ring-independent. -/

namespace OMA672G

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

end OMA672G
