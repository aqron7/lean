import Mathlib

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
