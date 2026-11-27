import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1
import Mathlib

-- Step Erdos672.erdos_672.variants.oblath.R1.H3: hypothesis H3 of reduction Erdos672.erdos_672.variants.oblath.R1
-- Credit: @aqron7

/-! Fermat's right triangle theorem: `y ^ 4 + z ^ 2 = x ^ 4` has no solutions with `y z ≠ 0`. -/

namespace OMA672

/-- A nontrivial solution of `y ^ 4 + z ^ 2 = x ^ 4`. -/
def F (x y z : ℤ) : Prop := y ≠ 0 ∧ z ≠ 0 ∧ y ^ 4 + z ^ 2 = x ^ 4

lemma F.x_ne_zero {x y z : ℤ} (h : F x y z) : x ≠ 0 := by
  rintro rfl
  have : 0 < y ^ 4 := by positivity [h.1]
  nlinarith [h.2.2, sq_nonneg z]

lemma F.neg {x y z : ℤ} (h : F x y z) : F (-x) y z :=
  ⟨h.1, h.2.1, by rw [h.2.2]; ring⟩

/-- `r ^ 2 - s ^ 2` is coprime to `r * s` when `r` and `s` are coprime. -/
lemma isCoprime_sq_sub {r s : ℤ} (h : IsCoprime r s) : IsCoprime (r ^ 2 - s ^ 2) (r * s) := by
  apply IsCoprime.mul_right
  · have : IsCoprime (s ^ 2) r := (isCoprime_comm.mp h).pow_left
    have h2 : IsCoprime (-(s ^ 2)) r := this.neg_left
    have : r ^ 2 - s ^ 2 = -(s ^ 2) + r * r := by ring
    rw [this]
    exact h2.add_mul_left_left r
  · have : IsCoprime (r ^ 2) s := h.pow_left
    have : r ^ 2 - s ^ 2 = r ^ 2 + (-s) * s := by ring
    rw [this]
    exact (h.pow_left).add_mul_right_left (-s)

/-- If `a * b = c ^ 2` with `a, b` coprime and `a > 0` then `a` is a square. -/
lemma sq_of_coprime_pos {a b c : ℤ} (hab : Int.gcd a b = 1) (h : a * b = c ^ 2) (ha : 0 < a) :
    ∃ i, a = i ^ 2 := by
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hab h
  rcases hi with hi | hi
  · exact ⟨i, hi⟩
  · exfalso; nlinarith [sq_nonneg i]

/-- The descent step, shared by both parity cases: `o` odd, `o ^ 2 + e ^ 2 = x ^ 2`,
coprime, `x > 0`, `o > 0`, `e ≠ 0`, and `w ^ 2 = o * e * 2` for some `w`. Produces a solution
with smaller first coordinate. -/
lemma step_even {o e x w : ℤ} (hco : Int.gcd o e = 1) (ho : o % 2 = 1) (hx : 0 < x)
    (hpy : o ^ 2 + e ^ 2 = x ^ 2) (hopos : 0 < o) (he : e ≠ 0) (hw : w ^ 2 = 2 * o * e) :
    ∃ a b c, F a b c ∧ a.natAbs < x.natAbs := by
  have ht : PythagoreanTriple o e x := by
    delta PythagoreanTriple; linear_combination hpy
  obtain ⟨r, s, h1, h2, h3, h4, -, h6⟩ := ht.coprime_classification' hco ho hx
  -- w is even
  have hw2 : Even w := by
    have : Even (w ^ 2) := ⟨o * e, by rw [hw]; ring⟩
    exact (Int.even_pow' two_ne_zero).mp this
  obtain ⟨w', hw'⟩ := hw2
  have hw'' : w = 2 * w' := by rw [hw']; ring
  rw [hw''] at hw
  have hs : w' ^ 2 = o * (r * s) := by
    have : (2 * w') ^ 2 = 2 * o * (2 * r * s) := by rw [hw, h2]
    nlinarith [this]
  have hcp : Int.gcd o (r * s) = 1 := by
    rw [h1]
    exact Int.isCoprime_iff_gcd_eq_one.mp (isCoprime_sq_sub (Int.isCoprime_iff_gcd_eq_one.mpr h4))
  have hrs0 : r * s ≠ 0 := by
    intro h0; apply he; rw [h2]; linear_combination 2 * h0
  have hrspos : 0 < r * s := by
    have : 0 ≤ o * (r * s) := by rw [← hs]; positivity
    exact lt_of_le_of_ne ((mul_nonneg_iff_of_pos_left hopos).mp this) (Ne.symm hrs0)
  obtain ⟨i, hi⟩ := sq_of_coprime_pos hcp hs.symm hopos
  have hcp' : Int.gcd (r * s) o = 1 := by rw [Int.gcd_comm]; exact hcp
  have hs' : r * s * o = w' ^ 2 := by rw [hs]; ring
  obtain ⟨d, hd⟩ := sq_of_coprime_pos hcp' hs' hrspos
  -- r and s have the same sign; r = ±j^2, s = ±k^2 with r ^ 2 = j ^ 4, s ^ 2 = k ^ 4
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one h4 hd
  have h4' : Int.gcd s r = 1 := by rw [Int.gcd_comm]; exact h4
  obtain ⟨k, hk⟩ := Int.sq_of_gcd_eq_one h4' (by rw [mul_comm]; exact hd)
  have hr0 : r ≠ 0 := left_ne_zero_of_mul hrs0
  have hs0 : s ≠ 0 := right_ne_zero_of_mul hrs0
  have hj2 : r ^ 2 = j ^ 4 := by rcases hj with hj | hj <;> rw [hj] <;> ring
  have hk2 : s ^ 2 = k ^ 4 := by rcases hk with hk | hk <;> rw [hk] <;> ring
  have hk0 : k ≠ 0 := by rintro rfl; apply hs0; simpa using hk2
  have hi0 : i ≠ 0 := by rintro rfl; rw [hi] at hopos; norm_num at hopos
  refine ⟨j, k, i, ⟨hk0, hi0, ?_⟩, ?_⟩
  · rw [← hk2, ← hj2]; linarith [hi, h1]
  · have hjx : |j| < x := by
      have h1' : |j| ≤ j ^ 2 := by
        have := Int.natAbs_le_self_sq j; rwa [Int.natCast_natAbs] at this
      have h2' : j ^ 2 ≤ j ^ 4 := by
        have := Int.le_self_sq (j ^ 2); nlinarith [this]
      have : 0 < s ^ 2 := by positivity
      nlinarith
    have := Int.natAbs_lt_natAbs_of_nonneg_of_lt (abs_nonneg j) hjx
    rwa [Int.natAbs_abs] at this

theorem no_F_aux (n : ℕ) : ∀ x y z : ℤ, x.natAbs = n → F x y z → False := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn h
  have ih' : ∀ a b c, F a b c → a.natAbs < x.natAbs → False :=
    fun a b c hf hlt => ih _ (hn ▸ hlt) a b c rfl hf
  clear ih hn
  wlog hx : 0 < x generalizing x
  · have hx0 := h.x_ne_zero
    exact this (-x) h.neg (fun a b c hf hlt => ih' a b c hf (by simpa using hlt)) (by omega)
  have hx0 := h.x_ne_zero
  -- x and y are coprime, else divide out a common prime
  have hcop : Int.gcd x y = 1 := by
    by_contra hg
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hpz : (p : ℤ) ^ 2 ∣ z := by
      rw [← Int.pow_dvd_pow_iff two_ne_zero]
      exact ⟨x1 ^ 4 - y1 ^ 4, by linear_combination h.2.2⟩
    obtain ⟨z1, rfl⟩ := hpz
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hf : F x1 y1 z1 := by
      refine ⟨fun h0 => h.1 (by simp [h0]), fun h0 => h.2.1 (by simp [h0]), ?_⟩
      have hp4 : (p : ℤ) ^ 4 ≠ 0 := pow_ne_zero _ hp0
      apply mul_left_cancel₀ hp4
      linear_combination h.2.2
    apply ih' x1 y1 z1 hf
    have hx1 : x1.natAbs ≠ 0 := by
      intro h0; apply hx0; simp [Int.natAbs_eq_zero.mp h0]
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_left (Nat.pos_of_ne_zero hx1) hp.one_lt
  -- y and z are coprime
  have hyz : Int.gcd y z = 1 := by
    by_contra hg
    obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    have hpy' := Int.natCast_dvd.mpr hpy
    have hpz' := Int.natCast_dvd.mpr hpz
    have h4 : (p : ℤ) ∣ x ^ 4 := by
      rw [← h.2.2]; exact dvd_add (dvd_pow hpy' (by norm_num)) (dvd_pow hpz' (by norm_num))
    have hpx : (p : ℤ) ∣ x := Int.Prime.dvd_pow' hp h4
    have hd : (p : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hpx hpy'
    rw [hcop] at hd
    have : p ∣ 1 := by exact_mod_cast hd
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hyz2 : IsCoprime (y ^ 2) z := (Int.isCoprime_iff_gcd_eq_one.mpr hyz).pow_left
  rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · -- y even: z odd, and (z, y^2, x^2) is a primitive triple
    have hz : z % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one z with hz | hz
      · exfalso
        have h2 : (2 : ℤ) ∣ (Int.gcd y z : ℤ) :=
          Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hy) (Int.dvd_of_emod_eq_zero hz)
        rw [hyz] at h2; norm_num at h2
      · exact hz
    have ht : PythagoreanTriple z (y ^ 2) (x ^ 2) := by
      delta PythagoreanTriple; linear_combination h.2.2
    have hg : Int.gcd z (y ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hyz2.symm
    obtain ⟨m, k, e1, e2, e3, e4, e5, e6⟩ := ht.coprime_classification' hg hz (by positivity)
    have hmk : 0 < m * k := by
      have : 0 < y ^ 2 := by positivity [h.1]
      nlinarith
    have hm : 0 < m := lt_of_le_of_ne e6 (by rintro rfl; simp at hmk)
    have hk : 0 < k := pos_of_mul_pos_right hmk hm.le
    rcases e5 with ⟨hm2, hk2⟩ | ⟨hm2, hk2⟩
    · obtain ⟨a, b, c, hf, hlt⟩ := step_even (o := k) (e := m) (x := x) (w := y)
        (by rw [Int.gcd_comm]; exact e4) hk2 hx (by linear_combination -e3) hk hm.ne'
        (by rw [e2]; ring)
      exact ih' a b c hf hlt
    · obtain ⟨a, b, c, hf, hlt⟩ := step_even (o := m) (e := k) (x := x) (w := y)
        e4 hm2 hx (by linear_combination -e3) hm hk.ne' (by rw [e2])
      exact ih' a b c hf hlt
  · -- y odd: (y^2, z, x^2) is a primitive triple
    have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
      delta PythagoreanTriple; linear_combination h.2.2
    have hg : Int.gcd (y ^ 2) z = 1 := Int.isCoprime_iff_gcd_eq_one.mp hyz2
    have hy2 : y ^ 2 % 2 = 1 := by rw [sq, Int.mul_emod, hy]; decide
    obtain ⟨m, k, e1, e2, e3, e4, e5, e6⟩ := ht.coprime_classification' hg hy2 (by positivity)
    have hk0 : k ≠ 0 := by rintro rfl; apply h.2.1; simp [e2]
    have hxy : x * y ≠ 0 := mul_ne_zero hx0 h.1
    have hf : F m k (x * y) := by
      refine ⟨hk0, hxy, ?_⟩
      have : (x * y) ^ 2 = (m ^ 2 + k ^ 2) * (m ^ 2 - k ^ 2) := by rw [mul_pow, e3, e1]
      linear_combination this
    apply ih' m k (x * y) hf
    have hk2 : 0 < k ^ 2 := by positivity
    have hmx : m < x := by nlinarith
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt e6 hmx

/-- Fermat: `y ^ 4 + z ^ 2 = x ^ 4` has no solution with `y z ≠ 0`. -/
theorem not_F {x y z : ℤ} (hy : y ≠ 0) (hz : z ≠ 0) : y ^ 4 + z ^ 2 ≠ x ^ 4 :=
  fun h => no_F_aux _ x y z rfl ⟨hy, hz, h⟩

end OMA672

namespace OMA672

/-- The product of `n, n + d, n + 2d` with `n, d` positive and coprime is never a fourth power. -/
theorem ap3_ne_pow_four {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1) :
    n * ((n + d) * (n + 2 * d)) ≠ q ^ 4 := by
  intro hq
  have c1 : Nat.Coprime (n + d) n := by
    rw [add_comm, Nat.coprime_add_self_left]; exact Nat.Coprime.symm hnd
  have c2 : Nat.Coprime (n + d) (n + 2 * d) := by
    have : n + 2 * d = (n + d) + d := by ring
    rw [this, Nat.coprime_self_add_right, Nat.coprime_add_self_left]; exact hnd
  have hcop : Nat.Coprime (n + d) (n * (n + 2 * d)) := Nat.Coprime.mul_right c1 c2
  have hAB : (n + d) * (n * (n + 2 * d)) = q ^ 4 := by rw [← hq]; ring
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hAB
  have hBA : (n * (n + 2 * d)) * (n + d) = q ^ 4 := by rw [← hAB]; ring
  obtain ⟨m, hm⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm) hBA
  have key : (n + d) ^ 2 = n * (n + 2 * d) + d ^ 2 := by ring
  rw [hv, hm] at key
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < n * (n + 2 * d) := by positivity
    simp [hm] at this
  apply not_F (x := (v : ℤ) ^ 2) (y := (m : ℤ)) (z := (d : ℤ))
    (by exact_mod_cast hm0) (by exact_mod_cast hd.ne')
  have key' : ((v : ℤ) ^ 4) ^ 2 = (m : ℤ) ^ 4 + (d : ℤ) ^ 2 := by exact_mod_cast key
  linear_combination -key'

end OMA672

theorem OMA.solution : OMA.R_Erdos672_erdos_672_variants_oblath_R1.H3 := by
  show Erdos672.Erdos672With 3 4
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 3 := by exact_mod_cast hk
      interval_cases k <;> simp <;> omega
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d} : Finset ℕ) := by simp; omega
  have h2 : n + d ∉ ({n + 2 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_singleton] at hq
  exact OMA672.ap3_ne_pow_four hn hd hnd hq
