/-
Silver finite-row bridge. Connects the generic cubic/quadratic normal-form
algebra of `SilverCrossover` to the ACTUAL finite Pascal-row packet — the
reversed g=3, k=1 ratio `ResidueSlices.revA`. This is the silver constant of
`alpha^3 = 7 + 7*alpha`, `S = 2 + (alpha+2)/(alpha+1)`,
`S^3 - 5*S^2 + 6*S - 1 = 0` (NOT the metallic silver ratio 1 + √2).

At the special multiplier `7/(3*alpha^2)`, the generic affine input of
`SilverCrossover` becomes exactly `7 + 7*z`. Finite-row bridge + convergence
facts only — no rates, no derivative convergence, no fixed-point existence,
no root-location.

Proof routes (keep every statement verbatim; minor lemma-name changes ok):
- T1 affineInput_center: unfold affineInput/affineIntercept/affineSlope, ring.
- T2 affineInput_silver: T1 defs + silverMultiplier + halpha + hpoly;
  field_simp/ring.
- T3 silverConstantFromRadical_isRoot: rational identity; unfold, clear the
  nonzero denom (alpha+1), LHS = -(alpha^3 - 7*alpha - 7)/(alpha+1)^3, then hpoly.
- T4 packetRatio_den_pos: `ResidueSlices.revA_pos` with k=0 (N=0 valid; no
  positive-row hyp).
- T5 tendsto_finiteMap: unfold finiteMap/packetRatio/limitingMap; specialize
  `ResidueSlices.tendsto_reversed_ratio` g=3 k=1 at the positive affine input.
- T6 finiteMap_center_sub_eq_centerError: rewrite affineInput_center.
- T7 tendsto_centerError: same reversed-ratio convergence at alpha^3, use
  halpha to identify (alpha^3)^(1/3) with alpha, subtract alpha.
- T8 tendstoUniformlyOn_finiteMap: apply
  `ResidueSlices.tendstoUniformlyOn_reversed_ratio` to the compact affine image
  `affineInput alpha mu '' K` (affine map continuous ⇒ image compact; hinput
  gives positivity on the image), pull back along `z ↦ affineInput alpha mu z`.
  Do not assume K nonempty.
- T9 cubicResidual_eq_packetDeviation_factor_of_fixed: put u = limitingMap;
  positivity ⇒ u^3 = affineInput; fixed point ⇒ packetDeviation = z - u; use
  z^3 - u^3 = (z-u)(z^2+zu+u^2); unfold cubicResidual/affineInput.
- T10 cubic_displacement_..._of_fixed: T9 +
  `SilverCrossover.cubicResidual_add_displacement`.
Certification: every completed target an active declaration; T4 no positive-row
hyp; packetDeviation sign is finiteMap - limitingMap; no strengthened
hypotheses. If a target cannot close, omit it and report its exact name.
-/
import RequestProject.SilverCrossover
import RequestProject.CompactUniform

open scoped Real Topology

namespace SilverFiniteRow

noncomputable def packetRatio (N : Nat) (x : Real) : Real :=
  ResidueSlices.revA 3 1 N x / ResidueSlices.revA 3 0 N x

def affineInput (alpha mu z : Real) : Real :=
  SilverCrossover.affineIntercept alpha mu +
    SilverCrossover.affineSlope alpha mu * z

noncomputable def finiteMap (N : Nat) (alpha mu z : Real) : Real :=
  packetRatio N (affineInput alpha mu z)

noncomputable def limitingMap (alpha mu z : Real) : Real :=
  affineInput alpha mu z ^ ((3 : Real)⁻¹)

noncomputable def packetDeviation (N : Nat) (alpha mu z : Real) : Real :=
  finiteMap N alpha mu z - limitingMap alpha mu z

noncomputable def centerError (N : Nat) (alpha : Real) : Real :=
  packetRatio N (alpha^3) - alpha

noncomputable def silverMultiplier (alpha : Real) : Real :=
  7 / (3 * alpha^2)

noncomputable def silverConstantFromRadical (alpha : Real) : Real :=
  2 + (alpha + 2) / (alpha + 1)

theorem affineInput_center (alpha mu : Real) :
    affineInput alpha mu alpha = alpha^3 := by
  unfold affineInput SilverCrossover.affineIntercept SilverCrossover.affineSlope
  ring

theorem affineInput_silver
    {alpha : Real} (halpha : alpha ≠ 0)
    (hpoly : alpha^3 = 7 + 7*alpha) (z : Real) :
    affineInput alpha (silverMultiplier alpha) z = 7 + 7*z := by
  unfold affineInput SilverCrossover.affineIntercept SilverCrossover.affineSlope
    silverMultiplier
  have h2 : alpha ^ 2 ≠ 0 := pow_ne_zero _ halpha
  field_simp
  linear_combination hpoly

theorem silverConstantFromRadical_isRoot
    {alpha : Real} (halpha : alpha ≠ -1)
    (hpoly : alpha^3 = 7 + 7*alpha) :
    silverConstantFromRadical alpha^3 -
        5*silverConstantFromRadical alpha^2 +
        6*silverConstantFromRadical alpha - 1 = 0 := by
  have h1 : alpha + 1 ≠ 0 := by
    intro h; exact halpha (by linarith)
  unfold silverConstantFromRadical
  field_simp
  linear_combination -hpoly

theorem packetRatio_den_pos (N : Nat) {x : Real} (hx : 0 < x) :
    0 < ResidueSlices.revA 3 0 N x :=
  ResidueSlices.revA_pos (Nat.zero_le N) hx

theorem tendsto_finiteMap
    (alpha mu z : Real) (hinput : 0 < affineInput alpha mu z) :
    Filter.Tendsto (fun N : Nat => finiteMap N alpha mu z)
      Filter.atTop (nhds (limitingMap alpha mu z)) := by
  have h := ResidueSlices.tendsto_reversed_ratio (g := 3) (k := 1)
    (by norm_num) (by norm_num) hinput
  unfold finiteMap packetRatio limitingMap
  simpa using h

theorem finiteMap_center_sub_eq_centerError
    (N : Nat) (alpha mu : Real) :
    finiteMap N alpha mu alpha - alpha = centerError N alpha := by
  unfold finiteMap centerError
  rw [affineInput_center]

theorem tendsto_centerError {alpha : Real} (halpha : 0 < alpha) :
    Filter.Tendsto (fun N : Nat => centerError N alpha)
      Filter.atTop (nhds 0) := by
  have hx : (0 : Real) < alpha ^ 3 := by positivity
  have h := ResidueSlices.tendsto_reversed_ratio (g := 3) (k := 1)
    (by norm_num) (by norm_num) hx
  have hval : (alpha ^ 3) ^ (((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = alpha := by
    rw [show (alpha ^ 3 : Real) = alpha ^ ((3 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul halpha.le]
    norm_num
  rw [hval] at h
  have : Filter.Tendsto
      (fun N : Nat => ResidueSlices.revA 3 1 N (alpha ^ 3) /
        ResidueSlices.revA 3 0 N (alpha ^ 3) - alpha)
      Filter.atTop (nhds (alpha - alpha)) := h.sub tendsto_const_nhds
  simpa [centerError, packetRatio] using this

theorem tendstoUniformlyOn_finiteMap
    (alpha mu : Real) {K : Set Real}
    (hK : IsCompact K)
    (hinput : ∀ z ∈ K, 0 < affineInput alpha mu z) :
    TendstoUniformlyOn
      (fun N z => finiteMap N alpha mu z)
      (fun z => limitingMap alpha mu z)
      Filter.atTop K := by
  have hcont : Continuous (fun z : Real => affineInput alpha mu z) := by
    unfold affineInput; fun_prop
  set K' : Set Real := (fun z : Real => affineInput alpha mu z) '' K with hK'
  have hK'c : IsCompact K' := hK.image hcont
  have hK'pos : K' ⊆ Set.Ioi (0 : Real) := by
    rintro y ⟨z, hz, rfl⟩
    exact hinput z hz
  have h := ResidueSlices.tendstoUniformlyOn_reversed_ratio (g := 3) (k := 1)
    (by norm_num) (by norm_num) hK'c hK'pos
  have hcomp := h.comp (g := fun z : Real => affineInput alpha mu z)
  have hsub : K ⊆ (fun z : Real => affineInput alpha mu z) ⁻¹' K' :=
    fun z hz => Set.mem_image_of_mem _ hz
  have := hcomp.mono hsub
  simpa [finiteMap, packetRatio, limitingMap, Function.comp_def] using this

theorem cubicResidual_eq_packetDeviation_factor_of_fixed
    {N : Nat} {alpha mu z : Real}
    (hinput : 0 < affineInput alpha mu z)
    (hfixed : finiteMap N alpha mu z = z) :
    SilverCrossover.cubicResidual alpha mu z =
      packetDeviation N alpha mu z *
        (z^2 + z*limitingMap alpha mu z +
          limitingMap alpha mu z^2) := by
  set u : Real := limitingMap alpha mu z with hu
  have hu3 : u ^ 3 = affineInput alpha mu z := by
    rw [hu, limitingMap, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hinput.le]
    norm_num
  have hdev : packetDeviation N alpha mu z = z - u := by
    rw [packetDeviation, hfixed, hu]
  rw [hdev, SilverCrossover.cubicResidual, ← affineInput, ← hu3]
  ring

theorem cubic_displacement_eq_packetDeviation_factor_of_fixed
    {N : Nat} {alpha mu delta : Real}
    (hinput : 0 < affineInput alpha mu (alpha + delta))
    (hfixed : finiteMap N alpha mu (alpha + delta) = alpha + delta) :
    delta^3 + 3*alpha*delta^2 +
        3*alpha^2*(1 - mu)*delta =
      packetDeviation N alpha mu (alpha + delta) *
        ((alpha + delta)^2 +
          (alpha + delta)*limitingMap alpha mu (alpha + delta) +
          limitingMap alpha mu (alpha + delta)^2) := by
  have h := cubicResidual_eq_packetDeviation_factor_of_fixed hinput hfixed
  rw [SilverCrossover.cubicResidual_add_displacement] at h
  exact h

end SilverFiniteRow
