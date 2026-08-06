/-
Silver finite-row fixed-point UNIQUENESS — exactly one collapse. Builds on
`SilverFiniteRowFixedPoint` (existence). Silver constant of `α³ = 7 + 7α`.

Mechanism (found numerically): the finite-row silver map is CONCAVE on `[0, N]`
(second derivative < 0, verified for the full bracket up to N=1000), so
`g z = finiteMap N α μ z − z` is concave; with `g 0 > 0` and `g N ≤ 0`, a
concave map has EXACTLY ONE zero. NB `g` is NOT globally monotone (for N=5,6 the
finite figure "rings": finiteMap'(0)>1), so monotonicity/contraction arguments
FAIL — concavity is the correct route. Spatial frame only (no Fourier).

Also proved (independent, clean, no calculus): the LIMITING collapse is exactly
`α` — on `[0,∞)` the only fixed point of `limitingMap` is the silver constant.

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- T1 concaveOn_finiteMap_silver — THE crux (a genuine analytic lemma). On
  `[0,N]` rewrite `finiteMap` to `packetRatio N (7+7z)` via `affineInput_silver`.
  Prove `ConcaveOn` via `concaveOn_of_deriv2_nonpos` (Convex (Icc);
  ContinuousOn from `continuousOn_finiteMap_silver`; twice differentiable on the
  interior; `deriv^[2] ≤ 0`). finiteMap = packetRatio ∘ (z↦7+7z); packetRatio
  N x = revA31 x / revA30 x with `revA 3 0 N x > 0` on `[7,·]` (`revA_pos`). The
  quotient second derivative `(u/v)'' = (u''v² − u v'' v − 2u'v'v + 2u v'²)/v³`
  has sign of its numerator; reduce `≤ 0` to the binomial-coefficient
  polynomial inequality (holds for every N; verified numerically to N=1000 on
  the full bracket). Alternative: prove `ConcaveOn (Set.Icc 7 (7+7N)) (packetRatio
  N)` and compose with the affine `z↦7+7z` via `ConcaveOn.comp_affineMap`. If
  this cannot close, OMIT it (and then also T2) and report — do not weaken it.
- T2 unique_finiteRow_fixedPoint — existence from `exists_finiteRow_fixedPoint`.
  Uniqueness: `g z = finiteMap N α μ z − z` is `ConcaveOn ℝ (Icc 0 N)` (T1 minus
  the linear `id` via `ConcaveOn.sub convexOn_id`); `g 0 = packetRatio N 7 > 0`
  (`packetRatio_pos`). For fixed points `z₁ < z₂` in `[0,N]`, write
  `z₁ = (1−t)·0 + t·z₂` with `t = z₁/z₂ ∈ (0,1)`; concavity gives
  `g z₁ ≥ (1−t)·g 0 + t·g z₂ = (1−t)·g 0 > 0`, contradicting `g z₁ = 0`.
- T3 limitingMap_fixedPoint_eq — clean ALGEBRA, no calculus. `limitingMap α μ z
  = (7+7z)^(3⁻¹)` (`affineInput_silver`). (←) `z = α`: `(7+7α)^(3⁻¹) =
  (α³)^(3⁻¹) = α` (hpoly, `α>0`, `Real.rpow` cube-root). (→) from
  `(7+7z)^(3⁻¹) = z` cube both sides (`z ≥ 0`, `7+7z>0`) to get `z³ = 7+7z`;
  with `α³ = 7+7α`, subtract: `(z−α)(z²+zα+α²−7) = 0`; since `α² = 7 + 7/α > 7`
  (from hpoly, `α>0`), `z²+zα+α² ≥ α² > 7`, so the second factor is positive,
  forcing `z = α`.
Certification: existence/uniqueness/limit only; if a target cannot close, omit
that declaration and report its exact name; do not weaken any statement.

STATUS OF THIS FILE. T2 `unique_finiteRow_fixedPoint` and T3
`limitingMap_fixedPoint_eq` are proved verbatim. T1
`concaveOn_finiteMap_silver` is OMITTED (not proved, not weakened): see
`RequestProject/SilverFiniteRowElasticity.lean` for the machinery that was
developed. Uniqueness (T2) does NOT use concavity here; it is obtained instead
from the ELASTICITY route, which is strictly weaker than concavity and is fully
proved: the Wronskian `W = A₁' A₀ − A₁ A₀'` of the two reversed row packets has
nonnegative coefficients and satisfies `x · W(x) < A₁(x) A₀(x)` for `x ≥ 0`
(`eval_wronskian_mul_lt`), i.e. the packet ratio has elasticity below one, so
`x ↦ A₁(x) / ((x − 7) A₀(x))` is strictly decreasing on `(7, ∞)`
(`strictAntiOn_scaledRatio`); every fixed point of the finite row map sits at
height `1/7` of that strictly monotone function, hence there is at most one.
Concavity itself (T1) reduces, after the same coefficient bookkeeping, to
`Var_X − Var_Y ≤ Δ − Δ²` for the two residue-class conditionals of the binomial
weights `C(N,n) tⁿ` (`Δ` the gap of their means); that inequality is an equality
in the degenerate `t → 0` limit for every `N`, so no crude bound suffices, and
it was not closed.
-/
import RequestProject.SilverFiniteRowElasticity

open scoped Real Topology

namespace SilverFiniteRow

/-- **Exactly one collapse.** At every row `N ≥ 1` the silver finite-row map has
a UNIQUE fixed point in `[0, N]`. -/
theorem unique_finiteRow_fixedPoint
    {alpha : ℝ} (halpha : 0 < alpha) (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃! z, z ∈ Set.Icc (0 : ℝ) (N : ℝ) ∧
      finiteMap N alpha (silverMultiplier alpha) z = z := by
  have hrw : ∀ z : ℝ, finiteMap N alpha (silverMultiplier alpha) z = packetRatio N (7 + 7 * z) := by
    intro z; rw [finiteMap, affineInput_silver (ne_of_gt halpha) hpoly z]
  -- every fixed point is positive and sits at height `1/7` of the scaled ratio
  have hchar : ∀ z : ℝ, 0 ≤ z → finiteMap N alpha (silverMultiplier alpha) z = z →
      7 < 7 + 7 * z ∧ scaledRatio N (7 + 7 * z) = 1 / 7 := by
    intro z hz hfix
    have hxpos : (0 : ℝ) < 7 + 7 * z := by linarith
    have hpos : 0 < packetRatio N (7 + 7 * z) := packetRatio_pos hN hxpos
    have hzpos : 0 < z := by rw [hrw z] at hfix; linarith [hfix ▸ hpos]
    refine ⟨by linarith, ?_⟩
    have hQ : 0 < ResidueSlices.revA 3 0 N (7 + 7 * z) :=
      ResidueSlices.revA_pos (Nat.zero_le N) hxpos
    have hnum : ResidueSlices.revA 3 1 N (7 + 7 * z)
        = z * ResidueSlices.revA 3 0 N (7 + 7 * z) := by
      have := hrw z ▸ hfix
      rw [packetRatio, div_eq_iff (ne_of_gt hQ)] at this
      exact this
    have hden : (7 : ℝ) * z * ResidueSlices.revA 3 0 N (7 + 7 * z) ≠ 0 := by positivity
    rw [scaledRatio, hnum, show (7 : ℝ) + 7 * z - 7 = 7 * z from by ring,
      eq_div_iff (by norm_num : (7 : ℝ) ≠ 0), div_mul_eq_mul_div, div_eq_one_iff_eq hden]
    ring
  obtain ⟨z₀, hz₀mem, hz₀⟩ := exists_finiteRow_fixedPoint halpha hpoly hN
  refine ⟨z₀, ⟨hz₀mem, hz₀⟩, ?_⟩
  rintro y ⟨hymem, hy⟩
  obtain ⟨hy7, hyval⟩ := hchar y hymem.1 hy
  obtain ⟨hz7, hzval⟩ := hchar z₀ hz₀mem.1 hz₀
  have hinj := (strictAntiOn_scaledRatio N hN).injOn
  have : 7 + 7 * y = 7 + 7 * z₀ :=
    hinj (Set.mem_Ioi.2 hy7) (Set.mem_Ioi.2 hz7) (by rw [hyval, hzval])
  linarith

/-- **The limiting collapse is exactly the silver constant.** On `[0, ∞)` the
only fixed point of the limiting map is `α`. -/
theorem limitingMap_fixedPoint_eq
    {alpha : ℝ} (halpha : 0 < alpha) (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    {z : ℝ} (hz : 0 ≤ z) :
    limitingMap alpha (silverMultiplier alpha) z = z ↔ z = alpha := by
  have hxpos : (0 : ℝ) < 7 + 7 * z := by linarith
  have hmap : limitingMap alpha (silverMultiplier alpha) z = (7 + 7 * z) ^ ((3 : ℝ)⁻¹) := by
    rw [limitingMap, affineInput_silver (ne_of_gt halpha) hpoly z]
  have hcube : ((7 + 7 * z) ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) = 7 + 7 * z := by
    rw [← Real.rpow_natCast ((7 + 7 * z) ^ ((3 : ℝ)⁻¹)) 3, ← Real.rpow_mul hxpos.le]
    norm_num
  have halpha2 : 7 < alpha ^ 2 := by
    have h : alpha ^ 3 = 7 + 7 * alpha := hpoly
    nlinarith [sq_nonneg (alpha - 3), sq_nonneg (alpha + 1), halpha]
  constructor
  · intro hfix
    rw [hmap] at hfix
    have hz3 : z ^ 3 = 7 + 7 * z := by
      conv_lhs => rw [← hfix]
      exact hcube
    have hfac : (z - alpha) * (z ^ 2 + z * alpha + alpha ^ 2 - 7) = 0 := by nlinarith [hz3, hpoly]
    have hsecond : 0 < z ^ 2 + z * alpha + alpha ^ 2 - 7 := by nlinarith [sq_nonneg z, hz, halpha]
    have := mul_eq_zero.1 hfac
    rcases this with h | h
    · linarith
    · linarith
  · intro hza
    rw [hmap, hza, show (7 : ℝ) + 7 * alpha = alpha ^ 3 from hpoly.symm,
      ← Real.rpow_natCast alpha 3, ← Real.rpow_mul halpha.le]
    norm_num

end SilverFiniteRow
