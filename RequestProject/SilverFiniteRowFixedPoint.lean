/-
Silver finite-row fixed-point EXISTENCE — the collapse is real. Certifies that
the finite-row silver map `finiteMap N α (silverMultiplier α)` has an ACTUAL
fixed point at every row `N ≥ 1`, i.e. the paper's coordinate collapse genuinely
happens at finite depth (not only in the `N → ∞` limit already given by
`tendsto_centerError`). Silver constant of `α³ = 7 + 7α` (NOT metallic `1+√2`).

At the silver multiplier `affineInput α (silverMultiplier α) z = 7 + 7z`
(`affineInput_silver`), so `finiteMap N α μ z = packetRatio N (7 + 7z)`.
The existence proof is a clean intermediate-value argument on the bracket
`[0, N]`, resting on one elementary binomial inequality — NO Fourier/spectral
machinery, NO remainder bounds, NO sharp rate. Numerically the fixed point is
unique on the positive axis and converges to `α = 3.04891734…`; only EXISTENCE
is claimed here (uniqueness and convergence-to-`α` are separate later targets).

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- T1 choose_succ_le_nat_mul: `Nat.choose_succ_right_eq` gives
  `C(N,m+1)·(m+1) = C(N,m)·(N−m) ≤ C(N,m)·N`; and `C(N,m+1) ≤ C(N,m+1)·(m+1)`
  since `1 ≤ m+1`. Nat arithmetic.
- T2 continuous_revA: unfold `revA`; a finite `Finset.sum` of
  `(C(N,gj+k):ℝ)·x^(q−j)` — `continuity`/`fun_prop`
  (`continuous_finsetSum`, `continuous_const.mul (continuous_pow _)`).
- T3 revA_one_le_nat_mul_revA_zero: termwise via T1 with `m = 3j`; each
  `x^(q−j) ≥ 0` (`x > 0`); `Finset.sum_le_sum`, then `Finset.mul_sum` on the RHS.
- T4 packetRatio_le_nat: `div_le_iff` with `revA 3 0 N x > 0` (`revA_pos`, k=0);
  reduce to T3.
- T5 packetRatio_pos: `div_pos` from `revA_pos` at k=1 (needs `1 ≤ N`) and k=0.
- T6 continuousOn_finiteMap_silver: on `Set.Icc 0 N` rewrite `finiteMap` by
  `affineInput_silver` to `packetRatio N (7+7z)`; `7+7z` continuous, `revA`
  continuous (T2), denominator `revA 3 0 N (7+7z) > 0` since `7+7z ≥ 7 > 0`
  (`revA_pos`) — `ContinuousOn.div`.
- T7 exists_finiteRow_fixedPoint: let `g z = finiteMap N α μ z − z`, continuous
  on `[0,N]` (T6). `g 0 = packetRatio N 7 > 0` (T5, `affineInput_silver` at
  z=0). `g N = packetRatio N (7+7N) − N ≤ 0` (T4, `affineInput_silver` at z=N).
  So `0 ∈ Set.Icc (g N) (g 0)`; `intermediate_value_Icc'` (with `0 ≤ (N:ℝ)`)
  gives `z ∈ [0,N]` with `g z = 0`, i.e. `finiteMap N α μ z = z`.
Certification: existence only; if a target cannot close, omit it and report its
exact name; do not weaken a statement.
-/
import RequestProject.SilverFiniteRowBridge

open scoped Real Topology

namespace SilverFiniteRow

/-- Elementary binomial inequality: `C(N, m+1) ≤ N · C(N, m)`. -/
theorem choose_succ_le_nat_mul (N m : ℕ) :
    N.choose (m + 1) ≤ N * N.choose m := by
  have h := Nat.choose_succ_right_eq N m
  calc N.choose (m + 1) ≤ N.choose (m + 1) * (m + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos m)
    _ = N.choose m * (N - m) := h
    _ ≤ N.choose m * N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = N * N.choose m := Nat.mul_comm _ _

/-- The reversed polynomial `revA g k N` is continuous in `x`. -/
theorem continuous_revA (g k N : ℕ) :
    Continuous (fun x : ℝ => ResidueSlices.revA g k N x) := by
  unfold ResidueSlices.revA
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_pow _)

/-- Termwise binomial domination of the `k=1` reversed polynomial by `N` times
the `k=0` one, on the positive axis. -/
theorem revA_one_le_nat_mul_revA_zero (N : ℕ) {x : ℝ} (hx : 0 < x) :
    ResidueSlices.revA 3 1 N x ≤ (N : ℝ) * ResidueSlices.revA 3 0 N x := by
  unfold ResidueSlices.revA
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : (N.choose (3 * j + 1) : ℝ) ≤ (N : ℝ) * (N.choose (3 * j + 0) : ℝ) := by
    have h := choose_succ_le_nat_mul N (3 * j)
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast at this ⊢
    simpa using this
  have hp : (0 : ℝ) ≤ x ^ (ResidueSlices.qIdx 3 N - j) := by positivity
  calc (N.choose (3 * j + 1) : ℝ) * x ^ (ResidueSlices.qIdx 3 N - j)
      ≤ ((N : ℝ) * (N.choose (3 * j + 0) : ℝ)) * x ^ (ResidueSlices.qIdx 3 N - j) :=
        mul_le_mul_of_nonneg_right h1 hp
    _ = (N : ℝ) * ((N.choose (3 * j + 0) : ℝ) * x ^ (ResidueSlices.qIdx 3 N - j)) := by ring

set_option linter.unusedVariables false in
/-- The finite packet ratio is bounded by the row index: `packetRatio N x ≤ N`.
The positive-row hypothesis `hN` is kept as requested; the termwise bound
`revA_one_le_nat_mul_revA_zero` in fact holds for every `N`, so the proof does
not use it. -/
theorem packetRatio_le_nat {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    packetRatio N x ≤ (N : ℝ) := by
  have hd : 0 < ResidueSlices.revA 3 0 N x := ResidueSlices.revA_pos (Nat.zero_le N) hx
  rw [packetRatio, div_le_iff₀ hd]
  exact revA_one_le_nat_mul_revA_zero N hx

/-- The finite packet ratio is strictly positive on the positive axis. -/
theorem packetRatio_pos {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    0 < packetRatio N x :=
  div_pos (ResidueSlices.revA_pos hN hx) (ResidueSlices.revA_pos (Nat.zero_le N) hx)

/-- The silver finite-row map is continuous on the bracket `[0, N]`. -/
theorem continuousOn_finiteMap_silver
    {alpha : ℝ} (halpha : alpha ≠ 0) (hpoly : alpha ^ 3 = 7 + 7 * alpha) (N : ℕ) :
    ContinuousOn
      (fun z : ℝ => finiteMap N alpha (silverMultiplier alpha) z)
      (Set.Icc (0 : ℝ) (N : ℝ)) := by
  have hrw : ∀ z : ℝ, finiteMap N alpha (silverMultiplier alpha) z
      = ResidueSlices.revA 3 1 N (7 + 7 * z) / ResidueSlices.revA 3 0 N (7 + 7 * z) := by
    intro z
    rw [finiteMap, affineInput_silver halpha hpoly z, packetRatio]
  simp only [hrw]
  have hlin : Continuous (fun z : ℝ => 7 + 7 * z) := by fun_prop
  refine ContinuousOn.div ((continuous_revA 3 1 N).comp hlin).continuousOn
    ((continuous_revA 3 0 N).comp hlin).continuousOn ?_
  intro z hz
  have hpos : (0 : ℝ) < 7 + 7 * z := by have := hz.1; linarith
  exact ne_of_gt (ResidueSlices.revA_pos (Nat.zero_le N) hpos)

/-- **The collapse is real.** At every row `N ≥ 1` the silver finite-row map has
an exact fixed point in `[0, N]` — the paper's coordinate collapse genuinely
occurs at finite depth. -/
theorem exists_finiteRow_fixedPoint
    {alpha : ℝ} (halpha : 0 < alpha) (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ z ∈ Set.Icc (0 : ℝ) (N : ℝ),
      finiteMap N alpha (silverMultiplier alpha) z = z := by
  have hcont : ContinuousOn
      (fun z : ℝ => finiteMap N alpha (silverMultiplier alpha) z - z)
      (Set.Icc (0 : ℝ) (N : ℝ)) :=
    (continuousOn_finiteMap_silver (ne_of_gt halpha) hpoly N).sub continuousOn_id
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hzero : finiteMap N alpha (silverMultiplier alpha) 0 = packetRatio N 7 := by
    rw [finiteMap, affineInput_silver (ne_of_gt halpha) hpoly 0]; norm_num
  have hg0 : 0 ≤ finiteMap N alpha (silverMultiplier alpha) 0 - 0 := by
    have hp : 0 < packetRatio N (7 : ℝ) := packetRatio_pos hN (by norm_num)
    rw [hzero]; linarith
  have hend : finiteMap N alpha (silverMultiplier alpha) (N : ℝ)
      = packetRatio N (7 + 7 * (N : ℝ)) := by
    rw [finiteMap, affineInput_silver (ne_of_gt halpha) hpoly ((N : ℝ))]
  have hgN : finiteMap N alpha (silverMultiplier alpha) (N : ℝ) - (N : ℝ) ≤ 0 := by
    have hle : packetRatio N (7 + 7 * (N : ℝ)) ≤ (N : ℝ) :=
      packetRatio_le_nat hN (by linarith)
    rw [hend]; linarith
  obtain ⟨z, hz, hzg⟩ := intermediate_value_Icc' hN0 hcont ⟨hgN, hg0⟩
  exact ⟨z, hz, by linarith [hzg]⟩

end SilverFiniteRow
