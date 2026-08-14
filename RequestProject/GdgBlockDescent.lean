/-
# Phase 4E: the constructive block descent for the `gd_g` critical residual

Phase 4D produced the parity-correct reciprocal residual `R_g`, a squarefree
self-reciprocal polynomial of exact even degree `2 * ((g-2)/2)` with neither
reciprocal fixed point `u = 1`, `u = -1` as a root.

This file performs the *block descent*: the explicit change of coordinate
`b = u + u⁻¹`.  We build a transparent polynomial `B_g` of exact degree
`d = (g-2)/2` in the block coordinate and prove the exact identity

    R_g(u) = u ^ d * B_g (u + u⁻¹)      (u ≠ 0),

together with the resulting root correspondence away from `u = 0`.
-/
import RequestProject.GdgReciprocalResidual

namespace GdgSquarefree

open Polynomial

/-! ### Definitions -/

/-- **Definition 1.** The reciprocal (Dickson-type) basis: the polynomials
`S_n` characterised by `S_n (u + u⁻¹) = u ^ n + u ^ (-n)`.  Note the
normalisation `S_0 = 2`, `S_1 = X` and the minus sign in the recurrence. -/
noncomputable def gdgReciprocalBasis : ℕ → Polynomial ℂ
  | 0 => Polynomial.C 2
  | 1 => Polynomial.X
  | n + 2 =>
      Polynomial.X * gdgReciprocalBasis (n + 1) -
        gdgReciprocalBasis n

/-- **Definition 2.** The block degree `d = (g-2)/2`, half of the exact
degree of the Phase 4D residual. -/
def gdgBlockDegree (g : ℕ) : ℕ := (g - 2) / 2

/-- **Definition 3.** The constructive block critical polynomial: the image of
the self-reciprocal residual `R_g` under the block coordinate `b = u + u⁻¹`.
The central coefficient occurs exactly once and the sum ranges over `Icc 1 d`
only, since `S_0 = 2`. -/
noncomputable def gdgBlockCriticalPolynomial (g : ℕ) : Polynomial ℂ :=
  Polynomial.C
      ((gdgReciprocalResidualPolynomial g).coeff (gdgBlockDegree g)) +
    ∑ r ∈ Finset.Icc 1 (gdgBlockDegree g),
      Polynomial.C
          ((gdgReciprocalResidualPolynomial g).coeff
            (gdgBlockDegree g + r)) *
        gdgReciprocalBasis r

/-! ### Targets 1–3: the reciprocal basis -/

/-- **Target 1.** The reciprocal basis evaluates to `u ^ n + u ^ (-n)` at the
block coordinate `u + u⁻¹`. -/
theorem gdgReciprocalBasis_eval
    (n : ℕ) {u : ℂ} (hu : u ≠ 0) :
    (gdgReciprocalBasis n).eval (u + u⁻¹) =
      u ^ n + (u⁻¹) ^ n := by
  have huu : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
  have key : ∀ n : ℕ,
      (gdgReciprocalBasis n).eval (u + u⁻¹) = u ^ n + (u⁻¹) ^ n ∧
        (gdgReciprocalBasis (n + 1)).eval (u + u⁻¹) =
          u ^ (n + 1) + (u⁻¹) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        exact ⟨by simp [gdgReciprocalBasis]; ring, by simp [gdgReciprocalBasis]⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        show (gdgReciprocalBasis (n + 2)).eval (u + u⁻¹) = _
        rw [gdgReciprocalBasis, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_X, ih.1, ih.2]
        have h1 : (u + u⁻¹) * (u ^ (n + 1) + (u⁻¹) ^ (n + 1))
            = (u ^ (n + 2) + (u⁻¹) ^ (n + 2))
              + (u * u⁻¹) * (u ^ n + (u⁻¹) ^ n) := by
          ring
        rw [h1, huu, one_mul]
        ring
  exact (key n).1

/-- **Target 2.** The reciprocal basis has exact degree `n`. -/
theorem gdgReciprocalBasis_natDegree (n : ℕ) :
    (gdgReciprocalBasis n).natDegree = n := by
  have key : ∀ n : ℕ,
      (gdgReciprocalBasis n).natDegree = n ∧
        (gdgReciprocalBasis (n + 1)).natDegree = n + 1 := by
    intro n
    induction n with
    | zero => exact ⟨by simp [gdgReciprocalBasis], by simp [gdgReciprocalBasis]⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        show (gdgReciprocalBasis (n + 2)).natDegree = n + 2
        rw [gdgReciprocalBasis]
        have hne : gdgReciprocalBasis (n + 1) ≠ 0 := by
          intro h
          rw [h] at ih
          simp at ih
        have hXmul : (Polynomial.X * gdgReciprocalBasis (n + 1)).natDegree = n + 2 := by
          rw [Polynomial.natDegree_X_mul hne, ih.2]
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
          (by rw [hXmul, ih.1]; omega), hXmul]
  exact (key n).1

/-- The top coefficient of the reciprocal basis in positive degree is `1`. -/
private theorem gdgReciprocalBasis_coeff_self (n : ℕ) (hn : 1 ≤ n) :
    (gdgReciprocalBasis n).coeff n = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      match n with
      | 0 => simp [gdgReciprocalBasis]
      | (m + 1) =>
          show (gdgReciprocalBasis (m + 2)).coeff (m + 2) = 1
          have hz : (gdgReciprocalBasis m).coeff (m + 2) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [gdgReciprocalBasis_natDegree]; omega)
          rw [gdgReciprocalBasis, Polynomial.coeff_sub, Polynomial.coeff_X_mul, hz,
            ih (by omega)]
          ring

/-- **Target 3.** For `n ≥ 1` the reciprocal basis is monic.  (`S_0 = C 2` is
not monic.) -/
theorem gdgReciprocalBasis_monic
    {n : ℕ} (hn : 1 ≤ n) :
    (gdgReciprocalBasis n).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [gdgReciprocalBasis_natDegree, gdgReciprocalBasis_coeff_self n hn]

/-! ### Targets 4–6: nonvanishing properties of the Phase 4D residual -/

/-- **Target 4.** The Phase 4D residual is nonzero: it has positive degree. -/
theorem gdgReciprocalResidualPolynomial_ne_zero
    {g : ℕ} (hg : 5 ≤ g) :
    gdgReciprocalResidualPolynomial g ≠ 0 := by
  intro h
  have hdeg := gdgReciprocalResidualPolynomial_natDegree hg
  rw [h, Polynomial.natDegree_zero] at hdeg
  omega

/-- **Target 5.** The constant coefficient of the residual is nonzero: it
equals the leading coefficient, because the residual is self-reciprocal. -/
theorem gdgReciprocalResidualPolynomial_coeff_zero_ne_zero
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgReciprocalResidualPolynomial g).coeff 0 ≠ 0 := by
  have hrev := gdgReciprocalResidualPolynomial_reverse hg
  have h0 : (gdgReciprocalResidualPolynomial g).coeff 0 =
      (gdgReciprocalResidualPolynomial g).leadingCoeff := by
    conv_lhs => rw [← hrev]
    exact Polynomial.coeff_zero_reverse _
  rw [h0]
  exact Polynomial.leadingCoeff_ne_zero.mpr
    (gdgReciprocalResidualPolynomial_ne_zero hg)

/-- **Target 6.** Every root of the residual is nonzero. -/
theorem gdgReciprocalResidualPolynomial_root_ne_zero
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ}
    (hu : (gdgReciprocalResidualPolynomial g).eval u = 0) :
    u ≠ 0 := by
  intro h0
  rw [h0, ← Polynomial.coeff_zero_eq_eval_zero] at hu
  exact gdgReciprocalResidualPolynomial_coeff_zero_ne_zero hg hu

/-! ### Targets 7–9: exact block degree -/

/-- The block degree is positive for `g ≥ 5`. -/
private theorem gdgBlockDegree_pos {g : ℕ} (hg : 5 ≤ g) :
    1 ≤ gdgBlockDegree g := by
  simp only [gdgBlockDegree]
  omega

/-- **Target 7.** The coefficient of the block polynomial in degree `d` is
exactly the leading coefficient of the residual. -/
theorem gdgBlockCriticalPolynomial_coeff_blockDegree
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgBlockCriticalPolynomial g).coeff (gdgBlockDegree g) =
      (gdgReciprocalResidualPolynomial g).coeff
        (2 * gdgBlockDegree g) := by
  have hd1 : 1 ≤ gdgBlockDegree g := gdgBlockDegree_pos hg
  set d := gdgBlockDegree g with hdef
  have hzero : ∀ r ∈ Finset.Icc 1 d, r ≠ d →
      (Polynomial.C ((gdgReciprocalResidualPolynomial g).coeff (d + r)) *
        gdgReciprocalBasis r).coeff d = 0 := by
    intro r hr hrd
    have hlt : r < d := lt_of_le_of_ne (Finset.mem_Icc.mp hr).2 hrd
    have hz : (gdgReciprocalBasis r).coeff d = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [gdgReciprocalBasis_natDegree]; exact hlt)
    rw [Polynomial.coeff_C_mul, hz, mul_zero]
  have hself : (gdgReciprocalBasis d).coeff d = 1 :=
    gdgReciprocalBasis_coeff_self d hd1
  rw [gdgBlockCriticalPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C, if_neg (by omega), zero_add,
    Finset.sum_eq_single_of_mem d (Finset.mem_Icc.mpr ⟨hd1, le_rfl⟩) hzero,
    Polynomial.coeff_C_mul, hself, mul_one, two_mul]

/-- The block polynomial has nonzero coefficient in degree `d`. -/
private theorem gdgBlockCriticalPolynomial_coeff_blockDegree_ne_zero
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgBlockCriticalPolynomial g).coeff (gdgBlockDegree g) ≠ 0 := by
  have hdeg : (gdgReciprocalResidualPolynomial g).natDegree =
      2 * gdgBlockDegree g := gdgReciprocalResidualPolynomial_natDegree hg
  rw [gdgBlockCriticalPolynomial_coeff_blockDegree hg, ← hdeg]
  exact Polynomial.leadingCoeff_ne_zero.mpr
    (gdgReciprocalResidualPolynomial_ne_zero hg)

/-- **Target 8.** The block polynomial has exact degree `d = (g-2)/2`:
degree one at `g = 5` and degree two at `g = 6`. -/
theorem gdgBlockCriticalPolynomial_natDegree
    {g : ℕ} (hg : 5 ≤ g) :
    (gdgBlockCriticalPolynomial g).natDegree = gdgBlockDegree g := by
  have hd1 : 1 ≤ gdgBlockDegree g := gdgBlockDegree_pos hg
  refine le_antisymm ?_
    (Polynomial.le_natDegree_of_ne_zero
      (gdgBlockCriticalPolynomial_coeff_blockDegree_ne_zero hg))
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [gdgBlockCriticalPolynomial, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C, if_neg (by omega), zero_add]
  refine Finset.sum_eq_zero ?_
  intro r hr
  have hlt : r < m := lt_of_le_of_lt (Finset.mem_Icc.mp hr).2 hm
  have hz : (gdgReciprocalBasis r).coeff m = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (by rw [gdgReciprocalBasis_natDegree]; exact hlt)
  rw [Polynomial.coeff_C_mul, hz, mul_zero]

/-- **Target 9.** The block polynomial is nonzero. -/
theorem gdgBlockCriticalPolynomial_ne_zero
    {g : ℕ} (hg : 5 ≤ g) :
    gdgBlockCriticalPolynomial g ≠ 0 := by
  intro h
  refine gdgBlockCriticalPolynomial_coeff_blockDegree_ne_zero hg ?_
  rw [h, Polynomial.coeff_zero]

/-! ### Targets 10–12: the exact descent identity and the root map -/

/-- The purely combinatorial descent identity for a palindromic coefficient
sequence of length `2 d + 1`. -/
private theorem gdgBlockDescent_sum_aux (c : ℕ → ℂ) (d : ℕ) {u : ℂ} (hu : u ≠ 0)
    (hsym : ∀ k, k ≤ 2 * d → c (2 * d - k) = c k) :
    ∑ i ∈ Finset.range (2 * d + 1), c i * u ^ i
      = u ^ d * (c d + ∑ r ∈ Finset.Icc 1 d, c (d + r) * (u ^ r + (u⁻¹) ^ r)) := by
  have hpow : ∀ r ∈ Finset.Icc 1 d, u ^ d * (u⁻¹) ^ r = u ^ (d - r) := by
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have h : u ^ d = u ^ (d - r) * u ^ r := by rw [← pow_add]; congr 1; omega
    rw [h, mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, mul_one]
  have hRHS : u ^ d * (c d + ∑ r ∈ Finset.Icc 1 d, c (d + r) * (u ^ r + (u⁻¹) ^ r))
      = c d * u ^ d + ((∑ r ∈ Finset.Icc 1 d, c (d + r) * u ^ (d + r))
        + ∑ r ∈ Finset.Icc 1 d, c (d + r) * u ^ (d - r)) := by
    rw [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    · ring
    · refine Finset.sum_congr rfl ?_
      intro r hr
      have h := hpow r hr
      have h2 : u ^ d * (c (d + r) * (u ^ r + (u⁻¹) ^ r))
          = c (d + r) * (u ^ d * u ^ r) + c (d + r) * (u ^ d * (u⁻¹) ^ r) := by ring
      rw [h2, h, ← pow_add]
  have hsplit : ∑ i ∈ Finset.range (2 * d + 1), c i * u ^ i
      = (∑ i ∈ Finset.range d, c i * u ^ i) + c d * u ^ d
        + ∑ i ∈ Finset.Ico (d + 1) (2 * d + 1), c i * u ^ i := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (d + 1))
        (by omega : d + 1 ≤ 2 * d + 1),
      ← Finset.range_eq_Ico, Finset.sum_range_succ]
  have hupper : ∑ i ∈ Finset.Ico (d + 1) (2 * d + 1), c i * u ^ i
      = ∑ r ∈ Finset.Icc 1 d, c (d + r) * u ^ (d + r) := by
    rw [Finset.sum_Ico_eq_sum_range,
      show Finset.Icc 1 d = Finset.Ico 1 (d + 1) by ext x; simp,
      Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) ?_
    intro i _
    congr 2 <;> omega
  have hlower : ∑ r ∈ Finset.Icc 1 d, c (d + r) * u ^ (d - r)
      = ∑ i ∈ Finset.range d, c i * u ^ i := by
    have step1 : ∑ r ∈ Finset.Icc 1 d, c (d + r) * u ^ (d - r)
        = ∑ j ∈ Finset.range d, c (d - 1 - j) * u ^ (d - 1 - j) := by
      rw [show Finset.Icc 1 d = Finset.Ico 1 (d + 1) by ext x; simp,
        Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1) ?_
      intro i hi
      simp only [Finset.mem_range] at hi
      have hval : c (d + (1 + i)) = c (d - (1 + i)) := by
        rw [← hsym (d - (1 + i)) (by omega)]
        congr 1
        omega
      rw [hval]
      congr 2 <;> omega
    rw [step1, Finset.sum_range_reflect (fun j => c j * u ^ j) d]
  rw [hRHS, hsplit, hupper, hlower]
  ring

/-- **Target 10.** The exact constructive descent identity
`R_g(u) = u ^ d * B_g (u + u⁻¹)` for `u ≠ 0`. -/
theorem gdgReciprocalResidual_eval_eq_block
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ} (hu : u ≠ 0) :
    (gdgReciprocalResidualPolynomial g).eval u =
      u ^ (gdgBlockDegree g) *
        (gdgBlockCriticalPolynomial g).eval (u + u⁻¹) := by
  have hdeg : (gdgReciprocalResidualPolynomial g).natDegree =
      2 * gdgBlockDegree g := gdgReciprocalResidualPolynomial_natDegree hg
  have hsym : ∀ k, k ≤ 2 * gdgBlockDegree g →
      (gdgReciprocalResidualPolynomial g).coeff (2 * gdgBlockDegree g - k) =
        (gdgReciprocalResidualPolynomial g).coeff k := by
    intro k hk
    conv_rhs => rw [← gdgReciprocalResidualPolynomial_reverse hg]
    rw [Polynomial.coeff_reverse,
      Polynomial.revAt_le (by rw [hdeg]; exact hk), hdeg]
  have hB : (gdgBlockCriticalPolynomial g).eval (u + u⁻¹)
      = (gdgReciprocalResidualPolynomial g).coeff (gdgBlockDegree g)
        + ∑ r ∈ Finset.Icc 1 (gdgBlockDegree g),
            (gdgReciprocalResidualPolynomial g).coeff (gdgBlockDegree g + r) *
              (u ^ r + (u⁻¹) ^ r) := by
    rw [gdgBlockCriticalPolynomial, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_finsetSum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Polynomial.eval_mul, Polynomial.eval_C, gdgReciprocalBasis_eval r hu]
  rw [Polynomial.eval_eq_sum_range, hdeg, hB]
  exact gdgBlockDescent_sum_aux _ _ hu hsym

/-- **Target 11.** Away from `u = 0` the block roots and the residual roots
correspond exactly. -/
theorem gdgBlockCriticalPolynomial_eval_eq_zero_iff
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ} (hu : u ≠ 0) :
    (gdgBlockCriticalPolynomial g).eval (u + u⁻¹) = 0 ↔
      (gdgReciprocalResidualPolynomial g).eval u = 0 := by
  rw [gdgReciprocalResidual_eval_eq_block hg hu]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hu)

/-- **Target 12.** Every residual root maps to a block root. -/
theorem gdgBlockCriticalPolynomial_root_of_residual_root
    {g : ℕ} (hg : 5 ≤ g) {u : ℂ}
    (hu : (gdgReciprocalResidualPolynomial g).eval u = 0) :
    (gdgBlockCriticalPolynomial g).eval (u + u⁻¹) = 0 :=
  (gdgBlockCriticalPolynomial_eval_eq_zero_iff hg
    (gdgReciprocalResidualPolynomial_root_ne_zero hg hu)).mpr hu

end GdgSquarefree
