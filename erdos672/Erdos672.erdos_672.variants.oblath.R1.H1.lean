import OMAReductions.R_Erdos672_erdos_672_variants_oblath_R1
import Mathlib

-- Step Erdos672.erdos_672.variants.oblath.R1.H1: hypothesis H1 of reduction Erdos672.erdos_672.variants.oblath.R1
-- Credit: @aqron7

/-! Euler: `x ^ 4 - x ^ 2 y ^ 2 + y ^ 4 = z ^ 2` forces `x y = 0` or `x ^ 2 = y ^ 2`. -/

namespace OMA672Q

/-- Nontrivial solution of the quartic. -/
def G (x y z : ℤ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ x ^ 2 ≠ y ^ 2 ∧ x ^ 4 - x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2

lemma G.z_ne_zero {x y z : ℤ} (h : G x y z) : z ≠ 0 := by
  rintro rfl
  have h1 := h.2.2.2
  have : 0 < x ^ 2 := by positivity [h.1]
  have : 0 < y ^ 2 := by positivity [h.2.1]
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]

lemma G.symm {x y z : ℤ} (h : G x y z) : G y x z :=
  ⟨h.2.1, h.1, fun e => h.2.2.1 e.symm, by linear_combination h.2.2.2⟩

/-- From `c ^ 2 = a ^ 2 + d ^ 2` and `b ^ 2 = a ^ 2 + 4 d ^ 2` we get a solution. -/
lemma G_of_T {a b c d : ℤ} (ha : a ≠ 0) (hd : d ≠ 0) (hc : c ^ 2 = a ^ 2 + d ^ 2)
    (hb : b ^ 2 = a ^ 2 + 4 * d ^ 2) : G a (|c| + |d|) ((|c| + |d|) * |b|) := by
  have hc2 : |c| ^ 2 = a ^ 2 + d ^ 2 := by rw [sq_abs]; exact hc
  have hd2 : |d| ^ 2 = d ^ 2 := sq_abs d
  have hb2 : |b| ^ 2 = a ^ 2 + 4 * d ^ 2 := by rw [sq_abs]; exact hb
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hcnn : 0 ≤ |c| := abs_nonneg c
  refine ⟨ha, by positivity, ?_, ?_⟩
  · intro e
    have : a ^ 2 = |c| ^ 2 + 2 * |c| * |d| + |d| ^ 2 := by rw [e]; ring
    nlinarith
  · have ha2 : a ^ 2 = |c| ^ 2 - |d| ^ 2 := by rw [hc2, hd2]; ring
    have hb3 : |b| ^ 2 = |c| ^ 2 + 3 * |d| ^ 2 := by rw [hb2, hc2, hd2]; ring
    rw [mul_pow]
    linear_combination (a ^ 2 + |c| ^ 2 - |d| ^ 2 - (|c| + |d|) ^ 2) * ha2
      - (|c| + |d|) ^ 2 * hb3


lemma three_dvd_of_sq_add {a d : ℤ} (h : (3 : ℤ) ∣ a ^ 2 + d ^ 2) : (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ d := by
  have h' : ((a : ZMod 3)) ^ 2 + ((d : ZMod 3)) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + d ^ 2) 3).mpr h
    push_cast at this; exact this
  have key : ∀ A D : ZMod 3, A ^ 2 + D ^ 2 = 0 → A = 0 ∧ D = 0 := by decide
  obtain ⟨h1, h2⟩ := key _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp h1, (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp h2⟩

lemma size_bound (A D : ℤ) (hA : 1 ≤ A) (hD : 1 ≤ D) :
    2 * (A + 2 * D) * (A + 4 * D) < (A ^ 2 + 2 * A * D + 4 * D ^ 2) ^ 2 := by
  have h1 : A ≤ A ^ 2 := by nlinarith
  have h2 : 1 ≤ A * D := by nlinarith
  have h3 : D ≤ D ^ 2 := by nlinarith
  set Z := A ^ 2 + 2 * A * D + 4 * D ^ 2 with hZdef
  have hZ : 7 ≤ Z := by rw [hZdef]; nlinarith
  have h4 : 7 * Z ≤ Z ^ 2 := by nlinarith
  have e : 2 * (A + 2 * D) * (A + 4 * D) = 2 * A ^ 2 + 12 * (A * D) + 16 * D ^ 2 := by ring
  have e2 : 7 * Z = 7 * A ^ 2 + 14 * (A * D) + 28 * D ^ 2 := by rw [hZdef]; ring
  nlinarith

/-- One of `x, y` even: descent through `c ^ 2 = a ^ 2 + d ^ 2`, `b ^ 2 = a ^ 2 + 4 d ^ 2`. -/
lemma step_one_even {x y z : ℤ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hz : 0 < z)
    (hcopI : IsCoprime x y) (hx2 : x % 2 = 1) (hy2 : y % 2 = 0)
    (hpt : (x ^ 2 - y ^ 2) ^ 2 + (x * y) ^ 2 = z ^ 2)
    (hcop2 : IsCoprime (x ^ 2 - y ^ 2) (x * y)) :
    ∃ a b c : ℤ, G a b c ∧ c.natAbs < z.natAbs := by
  have ht : PythagoreanTriple (x ^ 2 - y ^ 2) (x * y) z := by
    delta PythagoreanTriple; linear_combination hpt
  have hg : Int.gcd (x ^ 2 - y ^ 2) (x * y) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop2
  have hpar : (x ^ 2 - y ^ 2) % 2 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, y = 2 * j := ⟨y / 2, by omega⟩
    have : x ^ 2 - y ^ 2 = 1 + 2 * (2 * k ^ 2 + 2 * k - 2 * j ^ 2) := by rw [hk, hj]; ring
    rw [this, Int.add_mul_emod_self_left]; norm_num
  obtain ⟨m, n, e1, e2, e3, e4, -, e6⟩ := ht.coprime_classification' hg hpar hz
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  have hm0 : m ≠ 0 := by rintro rfl; apply hxy0; rw [e2]; ring
  have hn0 : n ≠ 0 := by rintro rfl; apply hxy0; rw [e2]; ring
  -- decompose x = b * a, m = c * a
  obtain ⟨a, b, c, ha, hbc, hxba, hmca⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left m hx0)
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbyn : b * y = 2 * c * n := by
    apply mul_left_cancel₀ ha0
    have e2' := e2
    rw [hxba, hmca] at e2'
    linear_combination e2'
  have hbodd : b % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one b with h | h
    · exfalso
      have : (2 : ℤ) ∣ x := by rw [hxba]; exact Dvd.dvd.mul_right (Int.dvd_of_emod_eq_zero h) _
      omega
    · exact h
  have hbc' : IsCoprime b c := Int.isCoprime_iff_gcd_eq_one.mpr hbc
  have hb2 : IsCoprime b 2 := by
    obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := ⟨b / 2, by omega⟩
    exact ⟨1, -k, by rw [hk]; ring⟩
  have hbn : b ∣ n := by
    have : b ∣ (2 * c) * n := ⟨y, by rw [← hbyn]⟩
    exact (hb2.mul_right hbc').dvd_of_dvd_mul_left this
  obtain ⟨d, rfl⟩ := hbn
  have hb0 : b ≠ 0 := by rintro rfl; simp at hxba; exact hx0 hxba
  have hy : y = 2 * c * d := by
    apply mul_left_cancel₀ hb0; linear_combination hbyn
  subst hy
  have hc0 : c ≠ 0 := by rintro rfl; simp at hmca; exact hm0 hmca
  have hd0 : d ≠ 0 := by rintro rfl; simp at hn0
  have hmn : IsCoprime m (b * d) := Int.isCoprime_iff_gcd_eq_one.mpr e4
  have had : IsCoprime (a : ℤ) d := by
    rw [hmca] at hmn
    exact hmn.of_mul_left_right.of_mul_right_right
  have hkey : (a : ℤ) ^ 2 * (b ^ 2 - c ^ 2) = d ^ 2 * (4 * c ^ 2 - b ^ 2) := by
    rw [hxba, hmca] at e1; linear_combination e1
  obtain ⟨k, hk⟩ : (a : ℤ) ^ 2 ∣ 4 * c ^ 2 - b ^ 2 := by
    have : (a : ℤ) ^ 2 ∣ d ^ 2 * (4 * c ^ 2 - b ^ 2) := ⟨b ^ 2 - c ^ 2, hkey.symm⟩
    exact (had.pow).dvd_of_dvd_mul_left this
  have ha2 : (a : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ ha0
  have hk2 : b ^ 2 - c ^ 2 = d ^ 2 * k := by
    apply mul_left_cancel₀ ha2; rw [hkey, hk]; ring
  have h3c : 3 * c ^ 2 = k * ((a : ℤ) ^ 2 + d ^ 2) := by linear_combination hk + hk2
  have h3b : 3 * b ^ 2 = k * ((a : ℤ) ^ 2 + 4 * d ^ 2) := by linear_combination hk + 4 * hk2
  have hk3 : k ∣ 3 := by
    obtain ⟨u, v, huv⟩ := (hbc'.symm.pow (m := 2) (n := 2))
    exact ⟨u * ((a : ℤ) ^ 2 + d ^ 2) + v * ((a : ℤ) ^ 2 + 4 * d ^ 2), by
      linear_combination (-3) * huv + u * h3c + v * h3b⟩
  have hkpos : 0 < k := by
    have : 0 < 3 * c ^ 2 := by positivity
    have : 0 < (a : ℤ) ^ 2 + d ^ 2 := by positivity
    nlinarith
  have hkle : k ≤ 3 := Int.le_of_dvd (by norm_num) hk3
  interval_cases k
  · -- k = 1: 3 ∣ a^2 + d^2
    exfalso
    obtain ⟨h1, h2⟩ := three_dvd_of_sq_add (a := a) (d := d) ⟨c ^ 2, by linarith⟩
    exact Int.prime_three.not_isUnit (had.isUnit_of_dvd' h1 h2)
  · exfalso; omega
  · -- k = 3
    have hcT : c ^ 2 = (a : ℤ) ^ 2 + d ^ 2 := by linarith
    have hbT : b ^ 2 = (a : ℤ) ^ 2 + 4 * d ^ 2 := by linarith
    refine ⟨a, |c| + |d|, (|c| + |d|) * |b|, G_of_T ha0 hd0 hcT hbT, ?_⟩
    have hZ0 : 0 ≤ (|c| + |d|) * |b| := by positivity
    have hzv : z = c ^ 2 * (a : ℤ) ^ 2 + b ^ 2 * d ^ 2 := by rw [e3, hmca]; ring
    have hlt : (|c| + |d|) * |b| < z := by
      have hA : 1 ≤ (a : ℤ) ^ 2 := by have := sq_pos_of_ne_zero ha0; omega
      have hD : 1 ≤ d ^ 2 := by have := sq_pos_of_ne_zero hd0; omega
      have e : ((|c| + |d|) * |b|) ^ 2 ≤ 2 * (c ^ 2 + d ^ 2) * b ^ 2 := by
        rw [mul_pow, sq_abs b]
        have : (|c| + |d|) ^ 2 ≤ 2 * (c ^ 2 + d ^ 2) := by
          nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d]
        nlinarith [sq_nonneg b]
      have hR : 2 * (c ^ 2 + d ^ 2) * b ^ 2
          = 2 * ((a : ℤ) ^ 2 + 2 * d ^ 2) * ((a : ℤ) ^ 2 + 4 * d ^ 2) := by rw [hcT, hbT]; ring
      have hz' : z = ((a : ℤ) ^ 2) ^ 2 + 2 * (a : ℤ) ^ 2 * d ^ 2 + 4 * (d ^ 2) ^ 2 := by
        rw [hzv, hcT, hbT]; ring
      have hsq : ((|c| + |d|) * |b|) ^ 2 < z ^ 2 := by
        have := size_bound ((a : ℤ) ^ 2) (d ^ 2) hA hD
        rw [hz']; linarith
      exact lt_of_pow_lt_pow_left₀ 2 hz.le hsq
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hZ0 hlt

/-- Both `x, y` odd: `(m, n, (x ^ 2 + y ^ 2) / 2)` is a smaller solution. -/
lemma step_odd_odd {x y z : ℤ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ^ 2 ≠ y ^ 2) (hz : 0 < z)
    (hx2 : x % 2 = 1) (hy2 : y % 2 = 1)
    (hpt : (x ^ 2 - y ^ 2) ^ 2 + (x * y) ^ 2 = z ^ 2)
    (hcop2 : IsCoprime (x ^ 2 - y ^ 2) (x * y)) :
    ∃ a b c : ℤ, G a b c ∧ c.natAbs < z.natAbs := by
  have ht : PythagoreanTriple (x * y) (x ^ 2 - y ^ 2) z := by
    delta PythagoreanTriple; linear_combination hpt
  have hg : Int.gcd (x * y) (x ^ 2 - y ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop2.symm
  have hpar : (x * y) % 2 = 1 := by rw [Int.mul_emod, hx2, hy2]; norm_num
  obtain ⟨m, n, e1, e2, e3, -, -, e6⟩ := ht.coprime_classification' hg hpar hz
  obtain ⟨w, hw⟩ : ∃ w, x ^ 2 + y ^ 2 = 2 * w := by
    obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    obtain ⟨j, hj⟩ : ∃ j, y = 2 * j + 1 := ⟨y / 2, by omega⟩
    exact ⟨2 * k ^ 2 + 2 * k + 2 * j ^ 2 + 2 * j + 1, by rw [hk, hj]; ring⟩
  have hd : x ^ 2 - y ^ 2 ≠ 0 := fun e => hxy (by linarith)
  have hm0 : m ≠ 0 := by rintro rfl; apply hd; rw [e2]; ring
  have hn0 : n ≠ 0 := by rintro rfl; apply hd; rw [e2]; ring
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  refine ⟨m, n, w, ⟨hm0, hn0, fun e => hxy0 (by rw [e1, e]; ring), ?_⟩, ?_⟩
  · have : 4 * (m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) = 4 * w ^ 2 := by
      linear_combination (-4 * (m ^ 2 - n ^ 2 + x * y)) * e1
        + (-(x ^ 2 - y ^ 2 + 2 * m * n)) * e2 + (x ^ 2 + y ^ 2 + 2 * w) * hw
    linarith
  · have hw0 : 0 < w := by
      have : 0 < x ^ 2 + y ^ 2 := by positivity
      omega
    have hsq : w ^ 2 < z ^ 2 := by
      have : 0 < (x ^ 2 - y ^ 2) ^ 2 := by positivity
      have h4 : 4 * w ^ 2 = (x ^ 2 + y ^ 2) ^ 2 := by rw [hw]; ring
      nlinarith [hpt]
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hw0.le (lt_of_pow_lt_pow_left₀ 2 hz.le hsq)

theorem G_aux (N : ℕ) : ∀ x y z : ℤ, z.natAbs = N → G x y z → False := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x y z hN h
  have ih' : ∀ a b c : ℤ, G a b c → c.natAbs < z.natAbs → False :=
    fun a b c hg hlt => ih _ (hN ▸ hlt) a b c rfl hg
  clear ih hN
  have hz0 := h.z_ne_zero
  -- WLOG z > 0
  wlog hz : 0 < z generalizing z
  · exact this (-z) ⟨h.1, h.2.1, h.2.2.1, by rw [h.2.2.2]; ring⟩
      (fun a b c hg hlt => ih' a b c hg (by simpa using hlt)) (by omega) (by omega)
  obtain ⟨hx0, hy0, hxy, heq⟩ := h
  -- coprime reduction
  have hcop : Int.gcd x y = 1 := by
    by_contra hg
    obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hg
    obtain ⟨x1, rfl⟩ := Int.natCast_dvd.mpr hpx
    obtain ⟨y1, rfl⟩ := Int.natCast_dvd.mpr hpy
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpz : (p : ℤ) ^ 2 ∣ z := by
      rw [← Int.pow_dvd_pow_iff two_ne_zero]
      exact ⟨x1 ^ 4 - x1 ^ 2 * y1 ^ 2 + y1 ^ 4, by rw [← heq]; ring⟩
    obtain ⟨z1, rfl⟩ := hpz
    apply ih' x1 y1 z1
    · refine ⟨fun e => hx0 (by rw [e, mul_zero]), fun e => hy0 (by rw [e, mul_zero]), ?_, ?_⟩
      · intro e; apply hxy; rw [mul_pow, mul_pow, e]
      · have hp4 : (p : ℤ) ^ 4 ≠ 0 := pow_ne_zero _ hp0
        apply mul_left_cancel₀ hp4; linear_combination heq
    · have hz1 : z1.natAbs ≠ 0 := by
        intro e; apply hz0; simp [Int.natAbs_eq_zero.mp e]
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
      exact lt_mul_left (Nat.pos_of_ne_zero hz1) (Nat.one_lt_pow two_ne_zero hp.one_lt)
  have hcopI : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  -- the Pythagorean triple
  have hpt : (x ^ 2 - y ^ 2) ^ 2 + (x * y) ^ 2 = z ^ 2 := by linear_combination heq
  have hcop2 : IsCoprime (x ^ 2 - y ^ 2) (x * y) := by
    apply IsCoprime.mul_right
    · have : x ^ 2 - y ^ 2 = -(y ^ 2) + x * x := by ring
      rw [this]; exact (hcopI.symm.pow_left.neg_left).add_mul_left_left x
    · have : x ^ 2 - y ^ 2 = x ^ 2 + (-y) * y := by ring
      rw [this]; exact hcopI.pow_left.add_mul_right_left (-y)
  rcases Int.emod_two_eq_zero_or_one x with hx2 | hx2 <;>
    rcases Int.emod_two_eq_zero_or_one y with hy2 | hy2
  · -- both even: impossible
    exfalso
    have : (2 : ℤ) ∣ (Int.gcd x y : ℤ) :=
      Int.dvd_coe_gcd (Int.dvd_of_emod_eq_zero hx2) (Int.dvd_of_emod_eq_zero hy2)
    rw [hcop] at this; norm_num at this
  · obtain ⟨a, b, c, hg, hlt⟩ := step_one_even hy0 hx0 hz hcopI.symm hy2 hx2
      (by linear_combination hpt) (by
        have := hcop2
        have e1 : y ^ 2 - x ^ 2 = -(x ^ 2 - y ^ 2) := by ring
        have e2 : y * x = x * y := by ring
        rw [e1, e2]; exact this.neg_left)
    exact ih' a b c hg hlt
  · obtain ⟨a, b, c, hg, hlt⟩ := step_one_even hx0 hy0 hz hcopI hx2 hy2 hpt hcop2
    exact ih' a b c hg hlt
  · obtain ⟨a, b, c, hg, hlt⟩ := step_odd_odd hx0 hy0 hxy hz hx2 hy2 hpt hcop2
    exact ih' a b c hg hlt

/-- Euler: `x ^ 4 - x ^ 2 y ^ 2 + y ^ 4 = z ^ 2` forces `x y = 0` or `x ^ 2 = y ^ 2`. -/
theorem quartic_trivial (x y z : ℤ) (h : x ^ 4 - x ^ 2 * y ^ 2 + y ^ 4 = z ^ 2) :
    x * y = 0 ∨ x ^ 2 = y ^ 2 := by
  by_contra hc
  push_neg at hc
  exact G_aux _ x y z rfl ⟨left_ne_zero_of_mul hc.1, right_ne_zero_of_mul hc.1, hc.2, h⟩

end OMA672Q

namespace OMA672H1

open OMA672Q

def cv : Fin 4 → ℕ := ![1, 2, 3, 6]

def ok (M c a : ℕ) : Bool := (List.range M).any (fun s => a % M == c * s * s % M)

def L16 : List (List ℕ) := [[1, 1, 1, 1, 1], [1, 1, 2, 3, 1], [1, 3, 2, 1, 1], [1, 3, 2, 1, 2], [1, 3, 2, 1, 3], [1, 3, 2, 1, 6], [1, 3, 6, 1, 3], [2, 1, 2, 3, 1], [2, 3, 6, 1, 3], [3, 1, 2, 3, 1], [3, 1, 6, 3, 1], [3, 1, 6, 3, 2], [3, 1, 6, 3, 3], [3, 1, 6, 3, 6], [3, 3, 3, 3, 3], [3, 3, 6, 1, 3], [6, 1, 2, 3, 1], [6, 3, 6, 1, 3]]

def L9 : List (List ℕ) := [[1, 1, 1, 1, 1], [1, 1, 2, 1, 6], [1, 1, 2, 3, 1], [1, 2, 1, 1, 2], [1, 2, 1, 6, 2], [1, 2, 2, 1, 2], [1, 2, 2, 1, 6], [1, 2, 3, 1, 2], [1, 2, 6, 1, 2], [1, 3, 2, 1, 1], [1, 3, 2, 1, 2], [1, 3, 2, 1, 3], [1, 3, 2, 1, 6], [1, 6, 2, 1, 3], [1, 6, 2, 1, 6], [2, 1, 1, 2, 1], [2, 1, 1, 2, 3], [2, 1, 2, 2, 1], [2, 1, 2, 3, 1], [2, 1, 3, 2, 1], [2, 1, 6, 2, 1], [2, 2, 1, 2, 3], [2, 2, 1, 6, 2], [2, 2, 2, 2, 2], [2, 3, 1, 2, 3], [2, 3, 1, 2, 6], [2, 6, 1, 2, 1], [2, 6, 1, 2, 2], [2, 6, 1, 2, 3], [2, 6, 1, 2, 6], [3, 1, 2, 3, 1], [3, 1, 2, 6, 1], [3, 2, 1, 1, 2], [3, 2, 1, 2, 2], [3, 2, 1, 3, 2], [3, 2, 1, 6, 2], [6, 1, 2, 1, 1], [6, 1, 2, 2, 1], [6, 1, 2, 3, 1], [6, 1, 2, 6, 1], [6, 2, 1, 3, 2], [6, 2, 1, 6, 2]]

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem loc16 : ∀ N D : Fin 16, (N.val % 2 = 1 ∨ D.val % 2 = 1) → ∀ k0 : Fin 4, ok 16 (cv k0) N = true →
    ∀ k1 : Fin 4, ok 16 (cv k1) (N + D) = true → ∀ k2 : Fin 4, ok 16 (cv k2) (N + 2 * D) = true →
    ∀ k3 : Fin 4, ok 16 (cv k3) (N + 3 * D) = true → ∀ k4 : Fin 4, ok 16 (cv k4) (N + 4 * D) = true →
    [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L16 := by decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem loc9 : ∀ N D : Fin 9, (N.val % 3 ≠ 0 ∨ D.val % 3 ≠ 0) → ∀ k0 : Fin 4, ok 9 (cv k0) N = true →
    ∀ k1 : Fin 4, ok 9 (cv k1) (N + D) = true → ∀ k2 : Fin 4, ok 9 (cv k2) (N + 2 * D) = true →
    ∀ k3 : Fin 4, ok 9 (cv k3) (N + 3 * D) = true → ∀ k4 : Fin 4, ok 9 (cv k4) (N + 4 * D) = true →
    [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L9 := by decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
theorem combine : ∀ k0 k1 k2 k3 k4 : Fin 4, [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L16 →
    [cv k0, cv k1, cv k2, cv k3, cv k4] ∈ L9 →
    (∃ r : Fin 100, r.val * r.val = cv k0 * cv k1 * cv k2 * cv k3 * cv k4) →
    [cv k0, cv k1, cv k2, cv k3, cv k4] = [1, 1, 1, 1, 1] ∨
    [cv k0, cv k1, cv k2, cv k3, cv k4] = [1, 3, 2, 1, 6] ∨
    [cv k0, cv k1, cv k2, cv k3, cv k4] = [6, 1, 2, 3, 1] := by decide

lemma ok_intro {M : ℕ} (hM : 0 < M) {x c b : ℕ} (h : x % M = (b ^ 2 * c) % M) : ok M c x = true := by
  simp only [ok, List.any_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨b % M, Nat.mod_lt _ hM, ?_⟩
  have hm : c * (b % M) * (b % M) ≡ c * b * b [MOD M] :=
    ((Nat.ModEq.refl c).mul (Nat.mod_modEq b M)).mul (Nat.mod_modEq b M)
  rw [h, show b ^ 2 * c = c * b * b by ring]
  exact hm.symm

/-- Four squares in a nonconstant AP: impossible. -/
lemma caseA {n d y0 y1 y2 y3 : ℕ} (hd : 0 < d) (h0 : n = y0 ^ 2) (h1 : n + d = y1 ^ 2)
    (h2 : n + 2 * d = y2 ^ 2) (h3 : n + 3 * d = y3 ^ 2) : False := by
  have hr1 : (y2 : ℤ) ^ 2 = 2 * (y1 : ℤ) ^ 2 - (y0 : ℤ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℤ) h0; have := congrArg (Nat.cast : ℕ → ℤ) h1
    have := congrArg (Nat.cast : ℕ → ℤ) h2; push_cast at *; linarith
  have hr2 : (y3 : ℤ) ^ 2 = 3 * (y1 : ℤ) ^ 2 - 2 * (y0 : ℤ) ^ 2 := by
    have := congrArg (Nat.cast : ℕ → ℤ) h0; have := congrArg (Nat.cast : ℕ → ℤ) h1
    have := congrArg (Nat.cast : ℕ → ℤ) h3; push_cast at *; linarith
  set a : ℤ := (y0 : ℤ); set b : ℤ := (y1 : ℤ); set c : ℤ := (y2 : ℤ); set e : ℤ := (y3 : ℤ)
  have hq := quartic_trivial (a + c) (b + e) (a * b - a * e + 3 * b * c + c * e) (by
    linear_combination (5 * a ^ 2 + 4 * a * c - 8 * b ^ 2 - 8 * b * e + c ^ 2 - 2 * e ^ 2) * hr1
      + (-2 * a ^ 2 + 5 * b ^ 2 + 4 * b * e + e ^ 2) * hr2)
  have hlt01 : y0 < y1 := by
    have : y0 ^ 2 < y1 ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hlt23 : y2 < y3 := by
    have : y2 ^ 2 < y3 ^ 2 := by omega
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hy1 : 0 < y1 := by omega
  have hy3 : 0 < y3 := by omega
  rcases hq with h | h
  · rcases mul_eq_zero.mp h with h | h
    · have hy2 : 0 < y2 := Nat.pos_of_ne_zero (by rintro rfl; simp at h2; omega)
      have : (0 : ℤ) < c := by show (0 : ℤ) < (y2 : ℤ); exact_mod_cast hy2
      have : (0 : ℤ) ≤ a := by positivity
      linarith
    · have : (0 : ℤ) < b := by show (0 : ℤ) < (y1 : ℤ); exact_mod_cast hy1
      have : (0 : ℤ) ≤ e := by positivity
      linarith
  · have hab : a + c = b + e := by
      have h0' : (0 : ℤ) ≤ a + c := by positivity
      have h1' : (0 : ℤ) ≤ b + e := by positivity
      nlinarith [sq_nonneg (a + c - (b + e)), sq_nonneg (a + c + (b + e))]
    have : (y0 : ℤ) + y2 < y1 + y3 := by exact_mod_cast (by omega : y0 + y2 < y1 + y3)
    linarith

/-- `3u², 2v², w², 6s²` in AP (either direction): impossible. -/
lemma caseB {u v w s : ℤ} (hu : u ≠ 0) (hs : 0 < s) (hv : 0 ≤ v)
    (hw : w ^ 2 = 4 * v ^ 2 - 3 * u ^ 2) (hs2 : s ^ 2 = v ^ 2 - u ^ 2) : False := by
  have hq := quartic_trivial u (v + s) ((v + s) * w) (by
    linear_combination (-s ^ 2 - 2 * s * v - v ^ 2) * hw + (s ^ 2 + 4 * s * v + u ^ 2 + 3 * v ^ 2) * hs2)
  rcases hq with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hu h
    · linarith
  · nlinarith [mul_nonneg hv hs.le]

lemma no_large_prime_two {n d p i j : ℕ} (hnd : n.gcd d = 1) (hp : p.Prime) (hp6 : ¬ p ∣ 6)
    (hi : i < 5) (hj : j < 5) (hij : i ≠ j) (hpi : p ∣ n + i * d) (hpj : p ∣ n + j * d) : False := by
  have hp5 : 5 ≤ p := by
    by_contra hlt; push_neg at hlt
    interval_cases p <;> first | (norm_num at hp; done) | (norm_num at hp6; done) | norm_num at hp hp6
  wlog hlt : i < j generalizing i j
  · exact this hj hi (Ne.symm hij) hpj hpi (by omega)
  have hdiff : p ∣ (j - i) * d := by
    have : n + j * d = (n + i * d) + (j - i) * d := by
      rw [Nat.sub_mul]; have : i * d ≤ j * d := Nat.mul_le_mul_right _ hlt.le; omega
    rw [this] at hpj
    exact (Nat.dvd_add_right hpi).mp hpj
  rcases (Nat.Prime.dvd_mul hp).mp hdiff with h | h
  · have : p ≤ j - i := Nat.le_of_dvd (by omega) h
    omega
  · have hpn : p ∣ n := (Nat.dvd_add_left (Dvd.dvd.mul_left h i)).mp hpi
    have : p ∣ Nat.gcd n d := Nat.dvd_gcd hpn h
    rw [hnd] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem ap5_ne_sq {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hnd : n.gcd d = 1)
    (h : n * ((n + d) * ((n + 2 * d) * ((n + 3 * d) * (n + 4 * d)))) = q ^ 2) : False := by
  have hpos : ∀ i : ℕ, 0 < n + i * d := fun i => by positivity
  have hsplit : ∀ i : ℕ, ∃ c b : ℕ, 0 < c ∧ 0 < b ∧ b ^ 2 * c = n + i * d ∧ Squarefree c :=
    fun i => Nat.sq_mul_squarefree_of_pos (hpos i)
  choose c b hc hb hbc hsf using hsplit
  have hprodA : ∏ i ∈ Finset.range 5, (n + i * d) = q ^ 2 := by
    rw [← h]; simp [Finset.prod_range_succ]; ring
  have hprod : (∏ i ∈ Finset.range 5, b i) ^ 2 * ∏ i ∈ Finset.range 5, c i = q ^ 2 := by
    rw [← hprodA, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hbc i)
  set B := ∏ i ∈ Finset.range 5, b i with hB
  set C := ∏ i ∈ Finset.range 5, c i with hC
  have hB0 : B ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (hb i).ne')
  have hBq : B ∣ q := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨C, hprod.symm⟩
  obtain ⟨r, hr⟩ := hBq
  have hCr : C = r ^ 2 := by
    have : B ^ 2 * C = B ^ 2 * r ^ 2 := by rw [hprod, hr]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  -- each squarefree part divides 6
  have hc6 : ∀ i, i < 5 → c i ∣ 6 := by
    intro i hi
    have hpf : ∀ p, p.Prime → p ∣ c i → p ∣ 6 := by
      intro p hp hpc
      by_contra hp6
      have hpC : p ∣ C := dvd_trans hpc (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi))
      rw [hCr] at hpC
      have hpr : p ∣ r := hp.dvd_of_dvd_pow hpC
      have hp2C : p ^ 2 ∣ C := by rw [hCr]; exact pow_dvd_pow_of_dvd hpr 2
      rw [hC, ← Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi)] at hp2C
      have hrest : ¬ p ∣ ∏ j ∈ (Finset.range 5).erase i, c j := by
        intro hpe
        obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpe
        obtain ⟨hji, hj5⟩ := Finset.mem_erase.mp hj
        exact no_large_prime_two hnd hp hp6 hi (Finset.mem_range.mp hj5) (Ne.symm hji)
          (dvd_trans hpc ⟨b i ^ 2, by rw [← hbc i]; ring⟩)
          (dvd_trans hpj ⟨b j ^ 2, by rw [← hbc j]; ring⟩)
      have hcop : Nat.Coprime (p ^ 2) (∏ j ∈ (Finset.range 5).erase i, c j) :=
        Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hrest)
      have : p * p ∣ c i := by rw [← sq]; exact hcop.dvd_of_dvd_mul_right hp2C
      exact (Nat.squarefree_iff_prime_squarefree.mp (hsf i)) p hp this
    rw [← Nat.prod_primeFactors_of_squarefree (hsf i)]
    have h6 : ∏ p ∈ (6 : ℕ).primeFactors, p = 6 :=
      Nat.prod_primeFactors_of_squarefree (by decide +kernel)
    rw [← h6]
    apply Finset.prod_dvd_prod_of_subset
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    exact ⟨hp.1, hpf p hp.1 hp.2.1, by norm_num⟩
  have hk : ∀ i, i < 5 → ∃ k : Fin 4, c i = cv k := by
    intro i hi
    have h1 := hc6 i hi
    have h2 : c i ≤ 6 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hc i
    interval_cases hci : c i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · norm_num at h1
    · norm_num at h1
    · exact ⟨3, rfl⟩
  obtain ⟨k0, hk0⟩ := hk 0 (by norm_num)
  obtain ⟨k1, hk1⟩ := hk 1 (by norm_num)
  obtain ⟨k2, hk2⟩ := hk 2 (by norm_num)
  obtain ⟨k3, hk3⟩ := hk 3 (by norm_num)
  obtain ⟨k4, hk4⟩ := hk 4 (by norm_num)
  have e0 : n = b 0 ^ 2 * cv k0 := by rw [← hk0, hbc 0]; ring
  have e1 : n + d = b 1 ^ 2 * cv k1 := by rw [← hk1, hbc 1]; ring
  have e2 : n + 2 * d = b 2 ^ 2 * cv k2 := by rw [← hk2, hbc 2]
  have e3 : n + 3 * d = b 3 ^ 2 * cv k3 := by rw [← hk3, hbc 3]
  have e4 : n + 4 * d = b 4 ^ 2 * cv k4 := by rw [← hk4, hbc 4]
  -- local conditions
  have hnotboth : ∀ p, p.Prime → ¬ (p ∣ n ∧ p ∣ d) := by
    rintro p hp ⟨h1, h2⟩
    have : p ∣ Nat.gcd n d := Nat.dvd_gcd h1 h2
    rw [hnd] at this; exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have h16 := loc16 ⟨n % 16, Nat.mod_lt _ (by norm_num)⟩ ⟨d % 16, Nat.mod_lt _ (by norm_num)⟩
    (by have := hnotboth 2 Nat.prime_two; simp only; omega) k0
    (ok_intro (by norm_num) (by simp only; rw [← e0]; omega)) k1
    (ok_intro (by norm_num) (by simp only; rw [← e1]; omega)) k2
    (ok_intro (by norm_num) (by simp only; rw [← e2]; omega)) k3
    (ok_intro (by norm_num) (by simp only; rw [← e3]; omega)) k4
    (ok_intro (by norm_num) (by simp only; rw [← e4]; omega))
  have h9 := loc9 ⟨n % 9, Nat.mod_lt _ (by norm_num)⟩ ⟨d % 9, Nat.mod_lt _ (by norm_num)⟩
    (by have := hnotboth 3 Nat.prime_three; simp only; omega) k0
    (ok_intro (by norm_num) (by simp only; rw [← e0]; omega)) k1
    (ok_intro (by norm_num) (by simp only; rw [← e1]; omega)) k2
    (ok_intro (by norm_num) (by simp only; rw [← e2]; omega)) k3
    (ok_intro (by norm_num) (by simp only; rw [← e3]; omega)) k4
    (ok_intro (by norm_num) (by simp only; rw [← e4]; omega))
  have hCv : C = cv k0 * cv k1 * cv k2 * cv k3 * cv k4 := by
    rw [hC]; simp [Finset.prod_range_succ, hk0, hk1, hk2, hk3, hk4]
  have hcvle : ∀ k : Fin 4, cv k ≤ 6 := by decide
  have hr100 : r < 100 := by
    have : r ^ 2 ≤ 6 * 6 * 6 * 6 * 6 := by
      rw [← hCr, hCv]
      have := hcvle k0; have := hcvle k1; have := hcvle k2; have := hcvle k3; have := hcvle k4
      gcongr <;> assumption
    nlinarith
  have hres := combine k0 k1 k2 k3 k4 h16 h9 ⟨⟨r, hr100⟩, by simp only; rw [← hCv, hCr]; ring⟩
  simp only [List.cons.injEq, and_true] at hres
  rcases hres with ⟨c0, c1, c2, c3, c4⟩ | ⟨c0, c1, c2, c3, c4⟩ | ⟨c0, c1, c2, c3, c4⟩
  · rw [c0] at e0; rw [c1] at e1; rw [c2] at e2; rw [c3] at e3
    exact caseA (n := n) (d := d) (y0 := b 0) (y1 := b 1) (y2 := b 2) (y3 := b 3) hd (by rw [e0]; ring) (by rw [e1]; ring) (by rw [e2]; ring) (by rw [e3]; ring)
  · rw [c1] at e1; rw [c2] at e2; rw [c3] at e3; rw [c4] at e4
    have z1 := congrArg (Nat.cast : ℕ → ℤ) e1; have z2 := congrArg (Nat.cast : ℕ → ℤ) e2
    have z3 := congrArg (Nat.cast : ℕ → ℤ) e3; have z4 := congrArg (Nat.cast : ℕ → ℤ) e4
    push_cast at z1 z2 z3 z4
    exact caseB (u := b 1) (v := b 2) (w := b 3) (s := b 4) (by exact_mod_cast (hb 1).ne')
      (by exact_mod_cast hb 4) (by positivity) (by linarith) (by linarith)
  · rw [c0] at e0; rw [c1] at e1; rw [c2] at e2; rw [c3] at e3
    have z0 := congrArg (Nat.cast : ℕ → ℤ) e0; have z1 := congrArg (Nat.cast : ℕ → ℤ) e1
    have z2 := congrArg (Nat.cast : ℕ → ℤ) e2; have z3 := congrArg (Nat.cast : ℕ → ℤ) e3
    push_cast at z0 z1 z2 z3
    exact caseB (u := b 3) (v := b 2) (w := b 1) (s := b 0) (by exact_mod_cast (hb 3).ne')
      (by exact_mod_cast hb 0) (by positivity) (by linarith) (by linarith)

end OMA672H1

theorem OMA.solution : OMA.R_Erdos672_erdos_672_variants_oblath_R1.H1 := by
  show Erdos672.Erdos672With 5 2
  intro s hs n hn d hd hnd hap q hq
  have hset := hap.2
  have hs' : s = {n, n + d, n + 2 * d, n + 3 * d, n + 4 * d} := by
    apply Finset.coe_injective
    rw [hset]
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, smul_eq_mul]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < 5 := by exact_mod_cast hk
      interval_cases k <;> simp <;> omega
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
      · exact ⟨2, by norm_num, by ring⟩
      · exact ⟨3, by norm_num, by ring⟩
      · exact ⟨4, by norm_num, by ring⟩
  rw [hs'] at hq
  have h1 : n ∉ ({n + d, n + 2 * d, n + 3 * d, n + 4 * d} : Finset ℕ) := by simp; omega
  have h2 : n + d ∉ ({n + 2 * d, n + 3 * d, n + 4 * d} : Finset ℕ) := by simp; omega
  have h3 : n + 2 * d ∉ ({n + 3 * d, n + 4 * d} : Finset ℕ) := by simp; omega
  have h4 : n + 3 * d ∉ ({n + 4 * d} : Finset ℕ) := by simp; omega
  rw [Finset.prod_insert h1, Finset.prod_insert h2, Finset.prod_insert h3, Finset.prod_insert h4,
    Finset.prod_singleton] at hq
  exact OMA672H1.ap5_ne_sq hn hd hnd hq
