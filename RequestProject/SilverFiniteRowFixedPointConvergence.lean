/-
Cubic-silver finite-row crossover, Phase B4A: convergence of the unique
silver-specialized finite-row fixed points.

The limiting silver map is `z ↦ (7 + 7z)^(1/3)`, whose unique nonnegative fixed
point is the silver constant `α` (`limitingMap_fixedPoint_eq`). Here we turn
that into a genuine convergence statement for the finite rows: the limiting map
strictly overshoots below `α` (T1) and strictly undershoots above `α` (T2);
since the finite-row maps converge pointwise (`tendsto_finiteMap`), for all
large rows the displacement `finiteMap N … z - z` keeps those signs at the two
bracket endpoints `α ∓ δ` (T3). Continuity plus the intermediate value theorem
then produces a fixed point inside the bracket, and the uniqueness theorem
`unique_finiteRow_fixedPoint` forces EVERY admissible fixed point of row `N` to
be that one (T4). Consequently the selected fixed point `silverFiniteRowFixedPoint`
(T5) converges to `α` (T6).
-/
import RequestProject.SilverFiniteRowUnique

open scoped Real Topology
open Filter

namespace SilverFiniteRow

/-- Cubing undoes the real cube root on the nonnegative axis. -/
private lemma rpow_third_cube {x : Real} (hx : 0 ≤ x) :
    (x ^ ((3 : Real)⁻¹)) ^ (3 : Nat) = x := by
  rw [← Real.rpow_natCast (x ^ ((3 : Real)⁻¹)) 3, ← Real.rpow_mul hx]
  norm_num

/-- Cube-root comparison, strict lower form: `z ^ 3 < x → z < x ^ (1/3)`. -/
private lemma lt_rpow_third_of_cube_lt {x z : Real} (hx : 0 ≤ x) (h : z ^ 3 < x) :
    z < x ^ ((3 : Real)⁻¹) := by
  by_contra hcon
  rw [not_lt] at hcon
  have := pow_le_pow_left₀ (Real.rpow_nonneg hx _) hcon 3
  rw [rpow_third_cube hx] at this
  linarith

/-- Cube-root comparison, strict upper form: `x < z ^ 3 → x ^ (1/3) < z`. -/
private lemma rpow_third_lt_of_lt_cube {x z : Real} (hx : 0 ≤ x) (hz : 0 ≤ z)
    (h : x < z ^ 3) : x ^ ((3 : Real)⁻¹) < z := by
  by_contra hcon
  rw [not_lt] at hcon
  have := pow_le_pow_left₀ hz hcon 3
  rw [rpow_third_cube hx] at this
  linarith

/-- The silver constant satisfies `7 < α ^ 2`. -/
private lemma seven_lt_sq_of_poly {alpha : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha) : 7 < alpha ^ 2 := by
  nlinarith [sq_nonneg (alpha - 3), sq_nonneg (alpha + 1), halpha]

/-- The cubic factorisation `z ^ 3 - (7 + 7z) = (z - α)(z ^ 2 + zα + α ^ 2 - 7)`. -/
private lemma cube_sub_affine_factor {alpha z : Real}
    (hpoly : alpha ^ 3 = 7 + 7 * alpha) :
    z ^ 3 - (7 + 7 * z) = (z - alpha) * (z ^ 2 + z * alpha + alpha ^ 2 - 7) := by
  linear_combination hpoly

/-- The silver limiting map in closed form. -/
private lemma limitingMap_silver_eq {alpha : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha) (z : Real) :
    limitingMap alpha (silverMultiplier alpha) z = (7 + 7 * z) ^ ((3 : Real)⁻¹) := by
  rw [limitingMap, affineInput_silver (ne_of_gt halpha) hpoly z]

/-- **Below the silver constant the limiting collapse pushes upward.** -/
theorem limitingMap_sub_self_pos_of_lt
    {alpha z : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    (hz : 0 ≤ z) (hzalpha : z < alpha) :
    0 < limitingMap alpha (silverMultiplier alpha) z - z := by
  have hx : (0 : Real) ≤ 7 + 7 * z := by linarith
  have hsq := seven_lt_sq_of_poly halpha hpoly
  have hsecond : 0 < z ^ 2 + z * alpha + alpha ^ 2 - 7 := by
    nlinarith [sq_nonneg z, mul_nonneg hz halpha.le]
  have hcube : z ^ 3 < 7 + 7 * z := by
    have hfac := cube_sub_affine_factor (alpha := alpha) (z := z) hpoly
    nlinarith [mul_pos (show (0 : Real) < alpha - z by linarith) hsecond]
  have := lt_rpow_third_of_cube_lt hx hcube
  rw [limitingMap_silver_eq halpha hpoly z]
  linarith

/-- **Above the silver constant the limiting collapse pushes downward.** -/
theorem limitingMap_sub_self_neg_of_lt
    {alpha z : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    (halphaz : alpha < z) :
    limitingMap alpha (silverMultiplier alpha) z - z < 0 := by
  have hzpos : 0 < z := lt_trans halpha halphaz
  have hx : (0 : Real) ≤ 7 + 7 * z := by linarith
  have hsq := seven_lt_sq_of_poly halpha hpoly
  have hsecond : 0 < z ^ 2 + z * alpha + alpha ^ 2 - 7 := by
    nlinarith [sq_nonneg z, mul_nonneg hzpos.le halpha.le]
  have hcube : 7 + 7 * z < z ^ 3 := by
    have hfac := cube_sub_affine_factor (alpha := alpha) (z := z) hpoly
    nlinarith [mul_pos (show (0 : Real) < z - alpha by linarith) hsecond]
  have := rpow_third_lt_of_lt_cube hx hzpos.le hcube
  rw [limitingMap_silver_eq halpha hpoly z]
  linarith

/-- **The bracket signs survive at every deep enough row.** -/
theorem eventually_finiteMap_bracket_sign
    {alpha delta : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    (hdelta : 0 < delta) (hdeltalpha : delta < alpha) :
    ∀ᶠ N : Nat in Filter.atTop,
      0 < finiteMap N alpha (silverMultiplier alpha) (alpha - delta) -
          (alpha - delta) ∧
        finiteMap N alpha (silverMultiplier alpha) (alpha + delta) -
          (alpha + delta) < 0 := by
  have hinput : ∀ z : Real, 0 ≤ z →
      0 < affineInput alpha (silverMultiplier alpha) z := by
    intro z hz
    rw [affineInput_silver (ne_of_gt halpha) hpoly z]
    linarith
  -- lower endpoint
  have hlow : (0 : Real) ≤ alpha - delta := by linarith
  have hlowlt : alpha - delta < alpha := by linarith
  have hposlim : 0 < limitingMap alpha (silverMultiplier alpha) (alpha - delta) -
      (alpha - delta) := limitingMap_sub_self_pos_of_lt halpha hpoly hlow hlowlt
  have htlow :
      Filter.Tendsto
        (fun N : Nat => finiteMap N alpha (silverMultiplier alpha) (alpha - delta) -
          (alpha - delta)) Filter.atTop
        (nhds (limitingMap alpha (silverMultiplier alpha) (alpha - delta) -
          (alpha - delta))) :=
    (tendsto_finiteMap alpha (silverMultiplier alpha) (alpha - delta)
      (hinput _ hlow)).sub tendsto_const_nhds
  have hevlow := htlow.eventually (eventually_gt_nhds hposlim)
  -- upper endpoint
  have hupp : (0 : Real) ≤ alpha + delta := by linarith
  have huppgt : alpha < alpha + delta := by linarith
  have hneglim : limitingMap alpha (silverMultiplier alpha) (alpha + delta) -
      (alpha + delta) < 0 := limitingMap_sub_self_neg_of_lt halpha hpoly huppgt
  have htupp :
      Filter.Tendsto
        (fun N : Nat => finiteMap N alpha (silverMultiplier alpha) (alpha + delta) -
          (alpha + delta)) Filter.atTop
        (nhds (limitingMap alpha (silverMultiplier alpha) (alpha + delta) -
          (alpha + delta))) :=
    (tendsto_finiteMap alpha (silverMultiplier alpha) (alpha + delta)
      (hinput _ hupp)).sub tendsto_const_nhds
  have hevupp := htupp.eventually (eventually_lt_nhds hneglim)
  exact hevlow.and hevupp

/-- **All finite-row collapses are eventually `ε`-close to the silver constant.** -/
theorem eventually_all_finiteRow_fixedPoints_near
    {alpha epsilon : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : Nat in Filter.atTop,
      ∀ z ∈ Set.Icc (0 : Real) (N : Real),
        finiteMap N alpha (silverMultiplier alpha) z = z →
          |z - alpha| < epsilon := by
  set delta : Real := min (epsilon / 2) (alpha / 2) with hdeltadef
  have hdelta : 0 < delta := lt_min (by linarith) (by linarith)
  have hdeltahalf : delta ≤ alpha / 2 := min_le_right _ _
  have hdeltaeps : delta ≤ epsilon / 2 := min_le_left _ _
  have hdeltalpha : delta < alpha := lt_of_le_of_lt hdeltahalf (by linarith)
  have hbracket := eventually_finiteMap_bracket_sign halpha hpoly hdelta hdeltalpha
  have hbig : ∀ᶠ N : Nat in Filter.atTop, alpha + delta ≤ (N : Real) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (alpha + delta))] with N hN
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  filter_upwards [hbracket, hbig, eventually_ge_atTop 1] with N hsign hNbig hN1
  obtain ⟨hposend, hnegend⟩ := hsign
  intro z hz hfix
  -- the bracket sits inside `[0, N]`
  have hsub : Set.Icc (alpha - delta) (alpha + delta) ⊆ Set.Icc (0 : Real) (N : Real) := by
    intro w hw
    exact ⟨le_trans (by linarith) hw.1, le_trans hw.2 hNbig⟩
  have hcont : ContinuousOn
      (fun w : Real => finiteMap N alpha (silverMultiplier alpha) w - w)
      (Set.Icc (alpha - delta) (alpha + delta)) :=
    (((continuousOn_finiteMap_silver (ne_of_gt halpha) hpoly N).sub
      continuousOn_id).mono hsub)
  obtain ⟨w, hwmem, hwzero⟩ :=
    intermediate_value_Icc' (by linarith : alpha - delta ≤ alpha + delta) hcont
      ⟨hnegend.le, hposend.le⟩
  have hwfix : finiteMap N alpha (silverMultiplier alpha) w = w := by
    have : finiteMap N alpha (silverMultiplier alpha) w - w = 0 := hwzero
    linarith
  -- uniqueness identifies `z` with the bracketed root `w`
  obtain ⟨u, _, huniq⟩ := unique_finiteRow_fixedPoint halpha hpoly hN1
  have hzu : z = u := huniq z ⟨hz, hfix⟩
  have hwu : w = u := huniq w ⟨hsub hwmem, hwfix⟩
  have hzw : z = w := by rw [hzu, hwu]
  have h1 : alpha - delta ≤ w := hwmem.1
  have h2 : w ≤ alpha + delta := hwmem.2
  rw [hzw, abs_lt]
  constructor <;> linarith

noncomputable def silverFiniteRowFixedPoint (N : Nat) (alpha : Real) : Real := by
  classical
  exact
    if h : ∃ z, z ∈ Set.Icc (0 : Real) (N : Real) ∧
        finiteMap N alpha (silverMultiplier alpha) z = z then
      Classical.choose h
    else
      0

/-- **The selected finite-row collapse is admissible and fixed** at every row `N ≥ 1`. -/
theorem silverFiniteRowFixedPoint_spec
    {alpha : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha)
    {N : Nat} (hN : 1 ≤ N) :
    silverFiniteRowFixedPoint N alpha ∈ Set.Icc (0 : Real) (N : Real) ∧
      finiteMap N alpha (silverMultiplier alpha)
          (silverFiniteRowFixedPoint N alpha) =
        silverFiniteRowFixedPoint N alpha := by
  classical
  have hex : ∃ z, z ∈ Set.Icc (0 : Real) (N : Real) ∧
      finiteMap N alpha (silverMultiplier alpha) z = z :=
    exists_finiteRow_fixedPoint halpha hpoly hN
  rw [silverFiniteRowFixedPoint, dif_pos hex]
  exact Classical.choose_spec hex

/-- **Convergence of the finite-row collapses to the silver constant.** -/
theorem tendsto_silverFiniteRowFixedPoint
    {alpha : Real} (halpha : 0 < alpha)
    (hpoly : alpha ^ 3 = 7 + 7 * alpha) :
    Filter.Tendsto
      (fun N : Nat => silverFiniteRowFixedPoint N alpha)
      Filter.atTop (nhds alpha) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hev := (eventually_all_finiteRow_fixedPoints_near halpha hpoly hepsilon).and
    (eventually_ge_atTop 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨hnear, hn1⟩ := hM n hn
  obtain ⟨hmem, hfix⟩ := silverFiniteRowFixedPoint_spec halpha hpoly hn1
  rw [Real.dist_eq]
  exact hnear _ hmem hfix

end SilverFiniteRow
