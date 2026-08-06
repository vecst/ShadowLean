/-
Polynomial elasticity machinery for the silver finite-row map.

This module supplies the analytic engine behind the UNIQUENESS of the finite-row
fixed point (`SilverFiniteRowUnique`).  The finite-row map is
`z ↦ packetRatio N (7 + 7z) = revA 3 1 N x / revA 3 0 N x` with `x = 7 + 7z`,
and the key structural fact proved here is that the *elasticity* of the packet
ratio never exceeds one:

  `x * (P' Q - P Q') (x) < P(x) Q(x)`   for `x > 0`,

where `P = revA 3 1 N`, `Q = revA 3 0 N`.  Equivalently `x ↦ P x / (x * Q x)` is
strictly decreasing, which pins down the fixed point uniquely.

The proof is purely combinatorial: writing `P` and `Q` as polynomials with
ascending coefficients `α d`, `β d`, the coefficient of `x^m` in
`x (P'Q - PQ') - PQ` equals `∑_{d} α d * β (m-d) * (2d - m - 1)`, and the
involution `d ↦ m + 1 - d` together with the log-concavity inequality
`C(N,a) C(N,a+e+2) ≤ C(N,a+2) C(N,a+e)` makes every antidiagonal sum
nonpositive.
-/
import RequestProject.SilverFiniteRowFixedPoint

open scoped Real Topology
open Finset Polynomial

namespace SilverFiniteRow

/-! ### Elementary binomial inequalities -/

/-- Moving two binomial arguments with a fixed sum closer together does not
decrease their product (one-step form). -/
theorem choose_step_mul_le (N : ℕ) {a b : ℕ} (hab : a ≤ b) :
    N.choose (b + 1) * N.choose a ≤ N.choose (a + 1) * N.choose b := by
  rcases lt_or_ge N b with hb | hb
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rcases lt_or_ge N a with ha | ha
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · have key : (N.choose (b + 1) * N.choose a) * ((a + 1) * (b + 1))
        ≤ (N.choose (a + 1) * N.choose b) * ((a + 1) * (b + 1)) := by
      have h1 : N.choose (a + 1) * (a + 1) = N.choose a * (N - a) := Nat.choose_succ_right_eq N a
      have h2 : N.choose (b + 1) * (b + 1) = N.choose b * (N - b) := Nat.choose_succ_right_eq N b
      calc (N.choose (b + 1) * N.choose a) * ((a + 1) * (b + 1))
          = (N.choose (b + 1) * (b + 1)) * N.choose a * (a + 1) := by ring
        _ = (N.choose b * (N - b)) * N.choose a * (a + 1) := by rw [h2]
        _ = (N.choose a * N.choose b) * ((N - b) * (a + 1)) := by ring
        _ ≤ (N.choose a * N.choose b) * ((N - a) * (b + 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.sub_le_sub_left hab N) (by omega))
        _ = (N.choose a * (N - a)) * N.choose b * (b + 1) := by ring
        _ = (N.choose (a + 1) * (a + 1)) * N.choose b * (b + 1) := by rw [h1]
        _ = (N.choose (a + 1) * N.choose b) * ((a + 1) * (b + 1)) := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- Moving two binomial arguments with a fixed sum closer together by two steps
does not decrease their product. -/
theorem choose_pair_le (N a d : ℕ) :
    N.choose a * N.choose (a + d + 2) ≤ N.choose (a + 2) * N.choose (a + d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Nat.mul_comm]
  · calc N.choose a * N.choose (a + d + 2)
        = N.choose ((a + d + 1) + 1) * N.choose a := by ring_nf
      _ ≤ N.choose (a + 1) * N.choose (a + d + 1) := choose_step_mul_le N (by omega)
      _ = N.choose ((a + d) + 1) * N.choose (a + 1) := by ring_nf
      _ ≤ N.choose (a + 1 + 1) * N.choose (a + d) := choose_step_mul_le N (by omega)
      _ = N.choose (a + 2) * N.choose (a + d) := by ring_nf

/-! ### The reversed row polynomials -/

/-- Ascending coefficient sequence of the reversed row polynomial `revA 3 k N`. -/
noncomputable def rowCoeff (N k d : ℕ) : ℝ :=
  if d ≤ ResidueSlices.qIdx 3 N then (N.choose (3 * (ResidueSlices.qIdx 3 N - d) + k) : ℝ) else 0

/-- The reversed row polynomial `revA 3 k N`, as a `Polynomial ℝ`. -/
noncomputable def rowPoly (N k : ℕ) : ℝ[X] :=
  ∑ d ∈ Finset.range (ResidueSlices.qIdx 3 N + 1), Polynomial.C (rowCoeff N k d) * X ^ d

theorem rowCoeff_nonneg (N k d : ℕ) : 0 ≤ rowCoeff N k d := by
  unfold rowCoeff; split <;> positivity

theorem rowPoly_coeff (N k d : ℕ) : (rowPoly N k).coeff d = rowCoeff N k d := by
  simp only [rowPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro hd
    simp only [Finset.mem_range, not_lt] at hd
    simp [rowCoeff, show ¬ (d ≤ ResidueSlices.qIdx 3 N) by omega]

theorem rowPoly_eval (N k : ℕ) (x : ℝ) :
    (rowPoly N k).eval x = ResidueSlices.revA 3 k N x := by
  simp only [rowPoly, ResidueSlices.revA, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_range] at hd
  have h1 : ResidueSlices.qIdx 3 N + 1 - 1 - d = ResidueSlices.qIdx 3 N - d := by omega
  rw [h1]
  have h2 : ResidueSlices.qIdx 3 N - (ResidueSlices.qIdx 3 N - d) = d := by omega
  simp [rowCoeff, h2]

/-! ### Coefficients of the products -/

theorem coeff_rowPoly_mul (N m : ℕ) :
    ((rowPoly N 1) * (rowPoly N 0)).coeff m
      = ∑ d ∈ Finset.range (m + 1), rowCoeff N 1 d * rowCoeff N 0 (m - d) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact Finset.sum_congr rfl fun d _ => by rw [rowPoly_coeff, rowPoly_coeff]

theorem coeff_derivative_rowPoly_mul (N n : ℕ) :
    ((Polynomial.derivative (rowPoly N 1)) * (rowPoly N 0)).coeff n
      = ∑ d ∈ Finset.range (n + 2), (d : ℝ) * (rowCoeff N 1 d * rowCoeff N 0 (n + 1 - d)) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  conv_rhs => rw [Finset.sum_range_succ']
  have h0 : ((0 : ℕ) : ℝ) * (rowCoeff N 1 0 * rowCoeff N 0 (n + 1 - 0)) = 0 := by simp
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [Polynomial.coeff_derivative, rowPoly_coeff, rowPoly_coeff]
  have : n + 1 - (k + 1) = n - k := by omega
  rw [this]
  push_cast
  ring

theorem coeff_rowPoly_mul_derivative (N n : ℕ) :
    ((rowPoly N 1) * (Polynomial.derivative (rowPoly N 0))).coeff n
      = ∑ d ∈ Finset.range (n + 2),
          ((n + 1 - d : ℕ) : ℝ) * (rowCoeff N 1 d * rowCoeff N 0 (n + 1 - d)) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  conv_rhs => rw [Finset.sum_range_succ]
  have hlast : ((n + 1 - (n + 1) : ℕ) : ℝ)
      * (rowCoeff N 1 (n + 1) * rowCoeff N 0 (n + 1 - (n + 1))) = 0 := by simp
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_range] at hd
  rw [Polynomial.coeff_derivative, rowPoly_coeff, rowPoly_coeff]
  have h1 : n + 1 - d = (n - d) + 1 := by omega
  rw [h1]
  push_cast
  ring

/-! ### The two antidiagonal inequalities -/

theorem rowCoeff_of_le (N k : ℕ) {d : ℕ} (h : d ≤ ResidueSlices.qIdx 3 N) :
    rowCoeff N k d = (N.choose (3 * (ResidueSlices.qIdx 3 N - d) + k) : ℝ) := if_pos h

theorem rowCoeff_of_gt (N k : ℕ) {d : ℕ} (h : ¬ d ≤ ResidueSlices.qIdx 3 N) :
    rowCoeff N k d = 0 := if_neg h

/-- Termwise comparison behind nonnegativity of the Wronskian coefficients. -/
theorem rowCoeff_cross_le (N m d : ℕ) (hd : m ≤ 2 * d) :
    rowCoeff N 1 (m - d) * rowCoeff N 0 d ≤ rowCoeff N 1 d * rowCoeff N 0 (m - d) := by
  by_cases hdq : d ≤ ResidueSlices.qIdx 3 N
  · by_cases hmd : m - d ≤ ResidueSlices.qIdx 3 N
    · rw [rowCoeff_of_le N 1 hdq, rowCoeff_of_le N 0 hdq, rowCoeff_of_le N 1 hmd,
        rowCoeff_of_le N 0 hmd]
      have hA : 3 * (ResidueSlices.qIdx 3 N - d) ≤ 3 * (ResidueSlices.qIdx 3 N - (m - d)) := by
        omega
      have hkey := choose_step_mul_le N hA
      exact_mod_cast (Nat.cast_le (α := ℝ)).2 hkey
    · rw [rowCoeff_of_gt N 1 hmd, rowCoeff_of_gt N 0 hmd]; simp
  · rw [rowCoeff_of_gt N 1 hdq, rowCoeff_of_gt N 0 hdq]; simp

/-- Termwise comparison behind the elasticity bound. -/
theorem rowCoeff_shift_le (N m d : ℕ) (hd : m + 1 ≤ 2 * d) (hd1 : 1 ≤ d) (hdm : d ≤ m) :
    rowCoeff N 1 d * rowCoeff N 0 (m - d) ≤ rowCoeff N 1 (m + 1 - d) * rowCoeff N 0 (d - 1) := by
  by_cases hdq : d ≤ ResidueSlices.qIdx 3 N
  · by_cases hmd : m - d ≤ ResidueSlices.qIdx 3 N
    · have hmd1 : m + 1 - d ≤ ResidueSlices.qIdx 3 N := by omega
      have hd1q : d - 1 ≤ ResidueSlices.qIdx 3 N := by omega
      rw [rowCoeff_of_le N 1 hdq, rowCoeff_of_le N 0 hmd, rowCoeff_of_le N 1 hmd1,
        rowCoeff_of_le N 0 hd1q]
      have hkey := choose_pair_le N (3 * (ResidueSlices.qIdx 3 N - d) + 1) (6 * d - 3 * m - 3)
      have he1 : 3 * (ResidueSlices.qIdx 3 N - d) + 1 + (6 * d - 3 * m - 3) + 2
          = 3 * (ResidueSlices.qIdx 3 N - (m - d)) + 0 := by omega
      have he2 : 3 * (ResidueSlices.qIdx 3 N - d) + 1 + 2
          = 3 * (ResidueSlices.qIdx 3 N - (d - 1)) + 0 := by omega
      have he3 : 3 * (ResidueSlices.qIdx 3 N - d) + 1 + (6 * d - 3 * m - 3)
          = 3 * (ResidueSlices.qIdx 3 N - (m + 1 - d)) + 1 := by omega
      rw [he1, he2, he3] at hkey
      exact_mod_cast (Nat.cast_le (α := ℝ)).2 (hkey.trans_eq (Nat.mul_comm _ _))
    · rw [rowCoeff_of_gt N 0 hmd]
      simp [mul_nonneg (rowCoeff_nonneg N 1 (m + 1 - d)) (rowCoeff_nonneg N 0 (d - 1))]
  · rw [rowCoeff_of_gt N 1 hdq]
    simp [mul_nonneg (rowCoeff_nonneg N 1 (m + 1 - d)) (rowCoeff_nonneg N 0 (d - 1))]

/-! ### Pairing the antidiagonal terms -/

/-- The pair `d ↔ m - d` contributes nonnegatively to the Wronskian coefficient. -/
theorem pair_term_wronskian_nonneg (N m d : ℕ) (hdm : d ≤ m) :
    0 ≤ (2 * (d : ℝ) - m) * (rowCoeff N 1 d * rowCoeff N 0 (m - d))
      + (2 * ((m - d : ℕ) : ℝ) - m) * (rowCoeff N 1 (m - d) * rowCoeff N 0 (m - (m - d))) := by
  have hmm : m - (m - d) = d := by omega
  have hcast : ((m - d : ℕ) : ℝ) = (m : ℝ) - d := by
    have : (d : ℝ) ≤ m := by exact_mod_cast hdm
    push_cast [Nat.cast_sub hdm]; ring
  rw [hmm, hcast]
  rcases le_or_gt m (2 * d) with h | h
  · have hkey := rowCoeff_cross_le N m d h
    have hc : (0 : ℝ) ≤ 2 * (d : ℝ) - m := by
      have : (m : ℝ) ≤ 2 * d := by exact_mod_cast h
      linarith
    nlinarith [mul_nonneg hc (sub_nonneg.2 hkey)]
  · have hle : m ≤ 2 * (m - d) := by omega
    have hkey := rowCoeff_cross_le N m (m - d) hle
    rw [hmm] at hkey
    have hc : (0 : ℝ) ≤ (m : ℝ) - 2 * d := by
      have : (2 * d : ℝ) ≤ m := by exact_mod_cast h.le
      linarith
    nlinarith [mul_nonneg hc (sub_nonneg.2 hkey)]

/-- The pair `e ↔ m + 1 - e` contributes nonpositively to the elasticity coefficient. -/
theorem pair_term_elasticity_nonpos (N m e : ℕ) (he1 : 1 ≤ e) (hem : e ≤ m) :
    (2 * (e : ℝ) - m - 1) * (rowCoeff N 1 e * rowCoeff N 0 (m - e))
      + (2 * ((m + 1 - e : ℕ) : ℝ) - m - 1)
          * (rowCoeff N 1 (m + 1 - e) * rowCoeff N 0 (m - (m + 1 - e))) ≤ 0 := by
  have hmm : m - (m + 1 - e) = e - 1 := by omega
  have hcast : ((m + 1 - e : ℕ) : ℝ) = (m : ℝ) + 1 - e := by
    have h : e ≤ m + 1 := by omega
    push_cast [Nat.cast_sub h]; ring
  rw [hmm, hcast]
  rcases le_or_gt (m + 1) (2 * e) with h | h
  · have hkey := rowCoeff_shift_le N m e h he1 hem
    have hc : (0 : ℝ) ≤ 2 * (e : ℝ) - m - 1 := by
      have : ((m : ℝ) + 1) ≤ 2 * e := by exact_mod_cast h
      linarith
    nlinarith [mul_nonneg hc (sub_nonneg.2 hkey)]
  · have h1 : m + 1 ≤ 2 * (m + 1 - e) := by omega
    have h2 : 1 ≤ m + 1 - e := by omega
    have h3 : m + 1 - e ≤ m := by omega
    have hkey := rowCoeff_shift_le N m (m + 1 - e) h1 h2 h3
    rw [hmm, show m + 1 - (m + 1 - e) = e by omega, show m + 1 - e - 1 = m - e by omega] at hkey
    have hc : (0 : ℝ) ≤ (m : ℝ) + 1 - 2 * e := by
      have : (2 * e : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h.le
      linarith
    nlinarith [mul_nonneg hc (sub_nonneg.2 hkey)]

/-- Every antidiagonal Wronskian coefficient is nonnegative. -/
theorem antidiag_wronskian_nonneg (N m : ℕ) :
    0 ≤ ∑ d ∈ Finset.range (m + 1),
      ((2 * (d : ℝ) - m) * (rowCoeff N 1 d * rowCoeff N 0 (m - d))) := by
  set T : ℕ → ℝ := fun d => (2 * (d : ℝ) - m) * (rowCoeff N 1 d * rowCoeff N 0 (m - d)) with hT
  have hrefl : ∑ d ∈ Finset.range (m + 1), T (m - d) = ∑ d ∈ Finset.range (m + 1), T d := by
    rw [← Finset.sum_range_reflect (fun d => T d) (m + 1)]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_range] at hd
    rw [show m + 1 - 1 - d = m - d by omega]
  have h2 : (2 : ℝ) * ∑ d ∈ Finset.range (m + 1), T d
      = ∑ d ∈ Finset.range (m + 1), (T d + T (m - d)) := by
    rw [Finset.sum_add_distrib, hrefl]; ring
  have hnn : 0 ≤ ∑ d ∈ Finset.range (m + 1), (T d + T (m - d)) := by
    refine Finset.sum_nonneg fun d hd => ?_
    simp only [Finset.mem_range] at hd
    exact pair_term_wronskian_nonneg N m d (by omega)
  linarith [h2, hnn]

/-- Every antidiagonal coefficient of `x (P'Q - PQ') - PQ` is nonpositive. -/
theorem antidiag_elasticity_nonpos (N m : ℕ) :
    ∑ d ∈ Finset.range (m + 1),
      ((2 * (d : ℝ) - m - 1) * (rowCoeff N 1 d * rowCoeff N 0 (m - d))) ≤ 0 := by
  set T : ℕ → ℝ := fun d => (2 * (d : ℝ) - m - 1) * (rowCoeff N 1 d * rowCoeff N 0 (m - d))
    with hT
  rw [Finset.sum_range_succ' T m]
  have hzero : T 0 ≤ 0 := by
    have h1 : (0 : ℝ) ≤ rowCoeff N 1 0 * rowCoeff N 0 (m - 0) :=
      mul_nonneg (rowCoeff_nonneg _ _ _) (rowCoeff_nonneg _ _ _)
    have h2 : (2 * ((0 : ℕ) : ℝ) - m - 1) ≤ 0 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      push_cast
      linarith
    simpa [hT] using mul_nonpos_of_nonpos_of_nonneg h2 h1
  have hmain : ∑ d ∈ Finset.range m, T (d + 1) ≤ 0 := by
    have hrefl : ∑ d ∈ Finset.range m, T (m - d) = ∑ d ∈ Finset.range m, T (d + 1) := by
      rw [← Finset.sum_range_reflect (fun d => T (d + 1)) m]
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [Finset.mem_range] at hd
      rw [show m - 1 - d + 1 = m - d by omega]
    have h2 : (2 : ℝ) * ∑ d ∈ Finset.range m, T (d + 1)
        = ∑ d ∈ Finset.range m, (T (d + 1) + T (m - d)) := by
      rw [Finset.sum_add_distrib, hrefl]; ring
    have hnp : ∑ d ∈ Finset.range m, (T (d + 1) + T (m - d)) ≤ 0 := by
      refine Finset.sum_nonpos fun d hd => ?_
      simp only [Finset.mem_range] at hd
      have hpair := pair_term_elasticity_nonpos N m (d + 1) (by omega) (by omega)
      have hidx : m + 1 - (d + 1) = m - d := by omega
      rw [hidx] at hpair
      simpa [hT] using hpair
    linarith [h2, hnp]
  linarith [hzero, hmain]

/-! ### Coefficients of the Wronskian combination -/

/-- The Wronskian `P'Q - PQ'` of the two reversed row polynomials. -/
noncomputable def rowWronskian (N : ℕ) : ℝ[X] :=
  Polynomial.derivative (rowPoly N 1) * rowPoly N 0
    - rowPoly N 1 * Polynomial.derivative (rowPoly N 0)

theorem coeff_rowWronskian (N n : ℕ) :
    (rowWronskian N).coeff n
      = ∑ d ∈ Finset.range (n + 2),
          ((2 * (d : ℝ) - (n + 1)) * (rowCoeff N 1 d * rowCoeff N 0 (n + 1 - d))) := by
  rw [rowWronskian, Polynomial.coeff_sub, coeff_derivative_rowPoly_mul,
    coeff_rowPoly_mul_derivative, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_range] at hd
  have hc : ((n + 1 - d : ℕ) : ℝ) = (n : ℝ) + 1 - d := by
    have h : d ≤ n + 1 := by omega
    have : ((n + 1 - d : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) - (d : ℝ) := by
      push_cast [Nat.cast_sub h]; ring
    rw [this]; push_cast; ring
  rw [hc]; ring

theorem coeff_rowWronskian_nonneg (N n : ℕ) : 0 ≤ (rowWronskian N).coeff n := by
  rw [coeff_rowWronskian]
  have := antidiag_wronskian_nonneg N (n + 1)
  simpa using this

/-- The elasticity polynomial `x (P'Q - PQ') - PQ`. -/
noncomputable def rowElasticity (N : ℕ) : ℝ[X] :=
  X * rowWronskian N - rowPoly N 1 * rowPoly N 0

theorem coeff_rowElasticity_nonpos (N n : ℕ) : (rowElasticity N).coeff n ≤ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (rowElasticity N).coeff 0 = - (rowCoeff N 1 0 * rowCoeff N 0 0) := by
      rw [rowElasticity, Polynomial.coeff_sub, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
        Polynomial.mul_coeff_zero, rowPoly_coeff, rowPoly_coeff]
      ring
    rw [h0]
    simpa using mul_nonneg (rowCoeff_nonneg N 1 0) (rowCoeff_nonneg N 0 0)
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hX : (X * rowWronskian N).coeff (k + 1) = (rowWronskian N).coeff k :=
      Polynomial.coeff_X_mul _ _
    rw [rowElasticity, Polynomial.coeff_sub, hX, coeff_rowWronskian, coeff_rowPoly_mul]
    have hsum : ∑ d ∈ Finset.range (k + 2),
          ((2 * (d : ℝ) - (k + 1)) * (rowCoeff N 1 d * rowCoeff N 0 (k + 1 - d)))
        - ∑ d ∈ Finset.range (k + 1 + 1), rowCoeff N 1 d * rowCoeff N 0 (k + 1 - d)
        = ∑ d ∈ Finset.range (k + 1 + 1),
            ((2 * (d : ℝ) - (k + 1) - 1) * (rowCoeff N 1 d * rowCoeff N 0 (k + 1 - d))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => by ring
    rw [hsum]
    have := antidiag_elasticity_nonpos N (k + 1)
    simpa using this

/-! ### Evaluation: the elasticity of the packet ratio is below one -/

theorem eval_rowWronskian_nonneg (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (rowWronskian N).eval x := by
  rw [Polynomial.eval_eq_sum_range]
  refine Finset.sum_nonneg fun n _ => mul_nonneg (coeff_rowWronskian_nonneg N n) (by positivity)

theorem rowCoeff_zero_pos (N k : ℕ) (hk : 3 * ResidueSlices.qIdx 3 N + k ≤ N) :
    0 < rowCoeff N k 0 := by
  rw [rowCoeff_of_le N k (Nat.zero_le _)]
  have : 0 < N.choose (3 * (ResidueSlices.qIdx 3 N - 0) + k) := by
    refine Nat.choose_pos ?_
    simpa using hk
  exact_mod_cast this

theorem eval_rowElasticity_neg (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    (rowElasticity N).eval x < 0 := by
  have hq : 3 * ResidueSlices.qIdx 3 N + 1 ≤ N := by
    have : ResidueSlices.qIdx 3 N = (N - 1) / 3 := rfl
    omega
  have h0 : (rowElasticity N).coeff 0 = - (rowCoeff N 1 0 * rowCoeff N 0 0) := by
    rw [rowElasticity, Polynomial.coeff_sub, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
      Polynomial.mul_coeff_zero, rowPoly_coeff, rowPoly_coeff]
    ring
  have hpos : 0 < rowCoeff N 1 0 * rowCoeff N 0 0 :=
    mul_pos (rowCoeff_zero_pos N 1 hq) (rowCoeff_zero_pos N 0 (by omega))
  rw [Polynomial.eval_eq_sum_range]
  have hmem : 0 ∈ Finset.range ((rowElasticity N).natDegree + 1) := Finset.mem_range.2 (by omega)
  rw [← Finset.add_sum_erase _ _ hmem]
  have hrest : ∑ n ∈ (Finset.range ((rowElasticity N).natDegree + 1)).erase 0,
      (rowElasticity N).coeff n * x ^ n ≤ 0 := by
    refine Finset.sum_nonpos fun n _ => ?_
    exact mul_nonpos_of_nonpos_of_nonneg (coeff_rowElasticity_nonpos N n) (by positivity)
  have hfirst : (rowElasticity N).coeff 0 * x ^ 0 < 0 := by
    rw [h0]; simpa using hpos
  linarith

/-- **Elasticity below one.** For `x > 0` the Wronskian of the reversed row
polynomials is dominated by their product divided by `x`. -/
theorem eval_wronskian_mul_lt (N : ℕ) (hN : 1 ≤ N) {x : ℝ} (hx : 0 ≤ x) :
    x * (rowWronskian N).eval x
      < ResidueSlices.revA 3 1 N x * ResidueSlices.revA 3 0 N x := by
  have h := eval_rowElasticity_neg N hN hx
  rw [rowElasticity, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_mul, rowPoly_eval, rowPoly_eval] at h
  linarith

/-! ### Strict antitonicity of the scaled packet ratio -/

/-- The packet ratio divided by the fixed-point variable, `P x / ((x - 7) Q x)`. -/
noncomputable def scaledRatio (N : ℕ) (x : ℝ) : ℝ :=
  ResidueSlices.revA 3 1 N x / ((x - 7) * ResidueSlices.revA 3 0 N x)

theorem hasDerivAt_scaledRatio (N : ℕ) {x : ℝ} (hx : 7 < x) :
    HasDerivAt (scaledRatio N)
      (((x - 7) * (rowWronskian N).eval x - ResidueSlices.revA 3 1 N x
            * ResidueSlices.revA 3 0 N x)
        / ((x - 7) * ResidueSlices.revA 3 0 N x) ^ 2) x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hQpos : 0 < ResidueSlices.revA 3 0 N x := ResidueSlices.revA_pos (Nat.zero_le N) hx0
  have hne : (x - 7) * ResidueSlices.revA 3 0 N x ≠ 0 := by positivity
  have hP : HasDerivAt (fun y : ℝ => ResidueSlices.revA 3 1 N y)
      ((Polynomial.derivative (rowPoly N 1)).eval x) x := by
    have := (rowPoly N 1).hasDerivAt x
    simpa [rowPoly_eval] using this
  have hQ : HasDerivAt (fun y : ℝ => ResidueSlices.revA 3 0 N y)
      ((Polynomial.derivative (rowPoly N 0)).eval x) x := by
    have := (rowPoly N 0).hasDerivAt x
    simpa [rowPoly_eval] using this
  have hlin : HasDerivAt (fun y : ℝ => y - 7) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 7
  have hden := hlin.mul hQ
  have hdiv := hP.div hden hne
  have heq : ((Polynomial.derivative (rowPoly N 1)).eval x * ((x - 7) * ResidueSlices.revA 3 0 N x)
        - ResidueSlices.revA 3 1 N x
            * (1 * ResidueSlices.revA 3 0 N x
                + (x - 7) * (Polynomial.derivative (rowPoly N 0)).eval x))
      / ((x - 7) * ResidueSlices.revA 3 0 N x) ^ 2
      = ((x - 7) * (rowWronskian N).eval x - ResidueSlices.revA 3 1 N x
            * ResidueSlices.revA 3 0 N x)
        / ((x - 7) * ResidueSlices.revA 3 0 N x) ^ 2 := by
    rw [rowWronskian]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, rowPoly_eval]
    ring_nf
  exact heq ▸ hdiv

theorem strictAntiOn_scaledRatio (N : ℕ) (hN : 1 ≤ N) :
    StrictAntiOn (scaledRatio N) (Set.Ioi (7 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 7) ?_ ?_
  · intro x hx
    exact (hasDerivAt_scaledRatio N (Set.mem_Ioi.1 hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx7 : 7 < x := Set.mem_Ioi.1 hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    rw [(hasDerivAt_scaledRatio N hx7).deriv]
    have hQpos : 0 < ResidueSlices.revA 3 0 N x := ResidueSlices.revA_pos (Nat.zero_le N) (by linarith)
    have hden : 0 < ((x - 7) * ResidueSlices.revA 3 0 N x) ^ 2 := by positivity
    have hW : 0 ≤ (rowWronskian N).eval x := eval_rowWronskian_nonneg N hx0
    have hnum : (x - 7) * (rowWronskian N).eval x
        - ResidueSlices.revA 3 1 N x * ResidueSlices.revA 3 0 N x < 0 := by
      have h1 : (x - 7) * (rowWronskian N).eval x ≤ x * (rowWronskian N).eval x := by
        nlinarith
      have h2 := eval_wronskian_mul_lt N hN hx0
      linarith
    exact div_neg_of_neg_of_pos hnum hden

end SilverFiniteRow
