import RequestProject.SphericalRadialTransport

/-!
# Spherical repair 7B.4: the angular potential, its tangent gradient and projected Hessian

This module proves the four Goal propositions stated below; their statements, and all the
definitions they are phrased with, are unchanged from the reviewed specification.  The setting
is the one of 7B.1–7B.3: the actual `L2` ambient space `Ambient V = WithLp 2 (ℝ × V)`, the
explicit orthogonal hyperplane `tangentPlane p = ker (innerSL ℝ p)` with its orthogonal
projection `tangentProjection p`, the moving frame `liftedFrame t e`, and the projected
derivative `covariant p v F = tangentProjection p (fderiv ℝ F p v)` of 7B.2.

The potential is the actual ambient scalar `angularPotential p = arccos ⟪north, p⟫ ^ 2 / 2`.
Everything below is obtained by *differentiating* it and the specified ambient gradient
extension; no diagonal Hessian is declared.

* `potential_gradient` (G1): at a unit `p` whose height `h = ⟪north, p⟫` satisfies `-1 < h < 1`,
  the ambient potential has the genuine Frechet derivative `gradientCoefficient p • innerSL ℝ
  north` (chain rule through `x ↦ arccos x ^ 2 / 2`, whose derivative at `h` is
  `-(arccos h / √(1 - h ^ 2))`); the specified field `angularGradient` is genuinely
  differentiable at `p`; its value is tangent at `p`; and it represents the differential on
  tangent vectors.  As stated, the last conjunct is restricted to tangent vectors: a tangent
  gradient does not represent the ambient differential on normal vectors, and no such claim is
  made here.
* `radial_values` (G2): for `0 < r < π` and unit `e` the height of `radialCurve e r` is
  `cos r`, which lies strictly between `-1` and `1` because `sin r > 0`; the potential value is
  `r ^ 2 / 2` (using `arccos (cos r) = r` on this branch); and the gradient is
  `r • liftedFrame r e e`.  The denominator `√(1 - cos r ^ 2) = sin r` is proved nonzero from
  the branch `0 < r < π`.
* `angular_hessian` (G3): the specified ambient gradient extension is differentiated (its
  derivative along `v` is `c'(h) ⟪north, v⟫ • (north - h • p) + c(h) • (-⟪north, v⟫ • p - h • v)`,
  with `c(h) = -(arccos h / √(1 - h ^ 2))`) and then projected with the 7B.2 `covariant`.  Since
  G1 supplies actual differentiability at every admissible point, the `fderiv` occurring in
  `angularHessian` is the genuine derivative and not a junk value.  Evaluating on the actual
  frame gives radial eigenvalue `1` and transverse eigenvalue `r cos r / sin r`, for every `W`
  (including `W = 0`).  At the equator `r = π / 2` the transverse eigenvalue is `0`, so a
  nonzero transverse vector has vanishing Hessian action while its frame image still has norm
  `‖W‖`; the radial action stays the identity.
* `composition_hessian` (G4): part 1 is exactly the 7A.2 `composition_derivative` result, not a
  re-proved algebraic stand-in; part 2 identifies the zero scalar component and the lifted
  vector component of that derivative with the Hessian action computed in G3.

The endpoints `r = 0` and `r = π` are excluded throughout: there `√(1 - h ^ 2) = 0` and the
ambient extension is not differentiated, so no smoothness is asserted there.

Scope caveat.  "Angular Hessian" here means the projected derivative of a field that has been
*proved* to be the tangent gradient of the angular potential.  This module does not identify
`arccos (height p)` with an intrinsic path-length distance, does not identify `tangentPlane p`
with a bundled manifold tangent space, and does not identify the projected connection with an
independently defined Levi-Civita connection; the L1 metric-recovery obligation stays open.
The chord distance inherited by the sphere subtype is not used anywhere, and no metric recovery
is claimed.
-/
namespace SphericalProofRequest7B4

open SphericalProofRequest7A1 SphericalProofRequest7A2 SphericalProofRequest7A3
open SphericalProofRequest7B1 SphericalProofRequest7B2 SphericalProofRequest7B3

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

noncomputable def north : Ambient V := toAmbient (1, 0)

noncomputable def height (p : Ambient V) : Real := inner Real north p

noncomputable def angularPotential (p : Ambient V) : Real :=
  (Real.arccos (height p)) ^ 2 / 2

noncomputable def gradientCoefficient (p : Ambient V) : Real :=
  -(Real.arccos (height p) / Real.sqrt (1 - (height p)^2))

-- A specified ambient extension; its gradient meaning must be proved in G1.
noncomputable def angularGradient (p : Ambient V) : Ambient V :=
  gradientCoefficient p • tangentProjection p north

-- Differentiate the actual field before projection; no diagonal formula here.
noncomputable def angularHessian (p v : Ambient V) : Ambient V :=
  covariant p v angularGradient

-- G1: actual differential and gradient meaning, including field differentiability.
def GoalPotentialGradient (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ p : Ambient V, ‖p‖=1 → -1 < height p → height p < 1 →
    HasFDerivAt angularPotential (gradientCoefficient p • innerSL Real north) p ∧
    DifferentiableAt Real angularGradient p ∧
    angularGradient p ∈ tangentPlane p ∧
    (∀ v : Ambient V, v ∈ tangentPlane p →
      fderiv Real angularPotential p v = inner Real (angularGradient p) v)

-- G2: verify the branch and radial values rather than stipulating them.
def GoalRadialValues (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0<r → r<Real.pi → ‖e‖=1 →
    -1 < height (radialCurve e r) ∧ height (radialCurve e r) < 1 ∧
    angularPotential (radialCurve e r)=r^2/2 ∧
    angularGradient (radialCurve e r)=r • liftedFrame r e e

-- G3: compute the actual projected derivative in every frame direction.
def GoalAngularHessian (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0<r → r<Real.pi → ‖e‖=1 → ∀ W : V,
    angularHessian (radialCurve e r) (liftedFrame r e W) =
      liftedFrame r e (radialProjection e W +
        (r * Real.cos r / Real.sin r) • transverseProjection e W)

-- G4: connect the actual full-log/product derivative to this differentiated field.
def GoalCompositionHessian (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0<r → r<Real.pi → ‖e‖=1 →
    HasFDerivAt (fun Y : V => fullLog (productMap r e Y)) (compositionDerivative r e) 0 ∧
    (∀ W : V,
      (fderiv Real (fun Y : V => fullLog (productMap r e Y)) 0 W).1 = 0 ∧
      liftedFrame r e ((fderiv Real (fun Y : V => fullLog (productMap r e Y)) 0 W).2) =
        angularHessian (radialCurve e r) (liftedFrame r e W))


/-! ### Supporting lemmas: the height function -/

/-- The height of a lifted pair is its scalar coordinate. -/
lemma height_toAmbient (x : Real × V) : height (toAmbient x) = x.1 := by
  rw [height, north, inner_toAmbient]
  simp

/-- Real symmetry of the inner product against the north pole. -/
lemma inner_north_left (p : Ambient V) : (inner Real p (north : Ambient V) : Real) = height p :=
  real_inner_comm north p

/-- The projection of the north pole onto the tangent hyperplane. -/
lemma tangentProjection_north (p : Ambient V) :
    tangentProjection p (north : Ambient V) = (north : Ambient V) - height p • p := by
  rw [tangentProjection_apply, inner_north_left]

/-- The specified ambient extension, written without the projection operator. -/
lemma angularGradient_eq (p : Ambient V) :
    angularGradient p = gradientCoefficient p • ((north : Ambient V) - height p • p) := by
  rw [angularGradient, tangentProjection_north]

/-- The height along the radial curve. -/
lemma height_radialCurve (e : V) (t : Real) : height (radialCurve e t) = Real.cos t := by
  rw [radialCurve_apply, height_toAmbient]

/-- The pairing of the north pole with a frame vector. -/
lemma inner_north_liftedFrame (r : Real) (e W : V) :
    (inner Real (north : Ambient V) (liftedFrame r e W) : Real)
      = -Real.sin r * inner Real e W := by
  show height (liftedFrame r e W) = _
  rw [liftedFrame_apply, height_toAmbient]

/-- On the branch `0 ≤ r ≤ π` the branch denominator is the sine. -/
lemma sqrt_one_sub_cos_sq {r : Real} (h1 : 0 ≤ r) (h2 : r ≤ Real.pi) :
    Real.sqrt (1 - (Real.cos r) ^ 2) = Real.sin r := by
  have hsq : 1 - (Real.cos r) ^ 2 = (Real.sin r) ^ 2 := by
    have := Real.sin_sq_add_cos_sq r; linarith
  rw [hsq, Real.sqrt_sq (Real.sin_nonneg_of_nonneg_of_le_pi h1 h2)]

/-- The tangential part of the north pole along the radial curve, in the moving frame. -/
lemma north_sub_smul_radialCurve (r : Real) (e : V) (he : ‖e‖ = 1) :
    (north : Ambient V) - Real.cos r • radialCurve e r
      = (-Real.sin r) • liftedFrame r e e := by
  rw [liftedFrame_self e he r, north, radialCurve_apply, ← map_smul, ← map_smul, ← map_sub]
  refine congrArg (toAmbient (V := V)) (Prod.ext ?_ ?_)
  · show (1 : Real) - Real.cos r * Real.cos r = -Real.sin r * -Real.sin r
    nlinarith [Real.sin_sq_add_cos_sq r]
  · show (0 : V) - Real.cos r • (Real.sin r • e) = (-Real.sin r) • (Real.cos r • e)
    module


/-! ### Supporting lemmas: differentiating the scalar branch -/

/-- The scalar derivative of `x ↦ arccos x ^ 2 / 2` on the open branch `-1 < x < 1`. -/
lemma hasDerivAt_arccos_sq_half {h : Real} (h1 : -1 < h) (h2 : h < 1) :
    HasDerivAt (fun x : Real => Real.arccos x ^ 2 / 2)
      (-(Real.arccos h / Real.sqrt (1 - h ^ 2))) h := by
  have hne1 : h ≠ -1 := by intro hh; rw [hh] at h1; linarith
  have hne2 : h ≠ 1 := by intro hh; rw [hh] at h2; linarith
  have hA : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - h ^ 2))) h :=
    Real.hasDerivAt_arccos hne1 hne2
  refine ((hA.pow 2).div_const 2).congr_deriv ?_
  ring

/-- The scalar derivative of the branch coefficient `x ↦ -(arccos x / √(1 - x ^ 2))`. -/
lemma hasDerivAt_coeffFun {h : Real} (h1 : -1 < h) (h2 : h < 1) :
    HasDerivAt (fun x : Real => -(Real.arccos x / Real.sqrt (1 - x ^ 2)))
      ((1 - Real.arccos h * h / Real.sqrt (1 - h ^ 2)) / (1 - h ^ 2)) h := by
  have hne1 : h ≠ -1 := by intro hh; rw [hh] at h1; linarith
  have hne2 : h ≠ 1 := by intro hh; rw [hh] at h2; linarith
  have hpos : (0 : Real) < 1 - h ^ 2 := by nlinarith
  have hs : 0 < Real.sqrt (1 - h ^ 2) := Real.sqrt_pos.mpr hpos
  have hsq : (Real.sqrt (1 - h ^ 2)) ^ 2 = 1 - h ^ 2 := Real.sq_sqrt hpos.le
  have hA : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - h ^ 2))) h :=
    Real.hasDerivAt_arccos hne1 hne2
  have hu : HasDerivAt (fun x : Real => 1 - x ^ 2) (-(2 * h)) h := by
    simpa using (hasDerivAt_pow 2 h).const_sub 1
  have hS : HasDerivAt (fun x : Real => Real.sqrt (1 - x ^ 2))
      ((-(2 * h)) / (2 * Real.sqrt (1 - h ^ 2))) h := hu.sqrt hpos.ne'
  refine ((hA.div hS hs.ne').neg).congr_deriv ?_
  set S : Real := Real.sqrt (1 - h ^ 2) with hSdef
  rw [← hsq]
  have hSne : S ≠ 0 := hs.ne'
  field_simp
  ring


/-! ### Supporting lemmas: differentiating the ambient fields -/

/-- The height is a continuous linear functional, hence its own derivative. -/
lemma hasFDerivAt_height (p : Ambient V) :
    HasFDerivAt (height : Ambient V → Real) (innerSL Real (north : Ambient V)) p := by
  have hfun : (height : Ambient V → Real) = ⇑(innerSL Real (north : Ambient V)) := by
    funext q; rw [height]; rfl
  rw [hfun]
  exact (innerSL Real (north : Ambient V)).hasFDerivAt

/-- G1's first conjunct: the actual Frechet derivative of the angular potential. -/
lemma hasFDerivAt_angularPotential {p : Ambient V} (h1 : -1 < height p) (h2 : height p < 1) :
    HasFDerivAt angularPotential
      (gradientCoefficient p • innerSL Real (north : Ambient V)) p := by
  have hfun : (angularPotential : Ambient V → Real)
      = (fun x : Real => Real.arccos x ^ 2 / 2) ∘ (height : Ambient V → Real) := rfl
  rw [hfun, gradientCoefficient]
  exact (hasDerivAt_arccos_sq_half h1 h2).comp_hasFDerivAt p (hasFDerivAt_height p)

/-- The derivative of the branch coefficient of the ambient gradient extension. -/
noncomputable def gradientCoefficientDeriv (p : Ambient V) : Real :=
  (1 - Real.arccos (height p) * height p / Real.sqrt (1 - (height p) ^ 2)) / (1 - (height p) ^ 2)

/-- The Frechet derivative of the specified ambient gradient extension. -/
noncomputable def angularGradientDeriv (p : Ambient V) : Ambient V →L[Real] Ambient V :=
  (innerSL Real (north : Ambient V)).smulRight
      (gradientCoefficientDeriv p • ((north : Ambient V) - height p • p)
        - gradientCoefficient p • p)
    - (gradientCoefficient p * height p) • ContinuousLinearMap.id Real (Ambient V)

lemma angularGradientDeriv_apply (p v : Ambient V) :
    angularGradientDeriv p v =
      (inner Real (north : Ambient V) v : Real) •
          (gradientCoefficientDeriv p • ((north : Ambient V) - height p • p)
            - gradientCoefficient p • p)
        - (gradientCoefficient p * height p) • v := by
  simp [angularGradientDeriv]

/-- The branch coefficient is genuinely differentiable at an admissible point. -/
lemma hasFDerivAt_gradientCoefficient {p : Ambient V} (h1 : -1 < height p) (h2 : height p < 1) :
    HasFDerivAt gradientCoefficient
      (gradientCoefficientDeriv p • innerSL Real (north : Ambient V)) p := by
  have hfun : (gradientCoefficient : Ambient V → Real)
      = (fun x : Real => -(Real.arccos x / Real.sqrt (1 - x ^ 2))) ∘ (height : Ambient V → Real) :=
    rfl
  rw [hfun, gradientCoefficientDeriv]
  exact (hasDerivAt_coeffFun h1 h2).comp_hasFDerivAt p (hasFDerivAt_height p)

/-- The specified ambient gradient extension is genuinely differentiable, with the derivative
`c'(h) ⟪north, v⟫ • (north - h • p) + c(h) • (-⟪north, v⟫ • p - h • v)`. -/
lemma hasFDerivAt_angularGradient {p : Ambient V} (h1 : -1 < height p) (h2 : height p < 1) :
    HasFDerivAt angularGradient (angularGradientDeriv p) p := by
  have hh := hasFDerivAt_height p
  have hc := hasFDerivAt_gradientCoefficient h1 h2
  have hHP : HasFDerivAt (fun q : Ambient V => height q • q)
      (height p • ContinuousLinearMap.id Real (Ambient V)
        + (innerSL Real (north : Ambient V)).smulRight p) p :=
    hh.smul (hasFDerivAt_id p)
  have hN : HasFDerivAt (fun q : Ambient V => (north : Ambient V) - height q • q)
      (0 - (height p • ContinuousLinearMap.id Real (Ambient V)
        + (innerSL Real (north : Ambient V)).smulRight p)) p :=
    (hasFDerivAt_const (north : Ambient V) p).sub hHP
  have hG := hc.smul hN
  have hfun : (angularGradient : Ambient V → Ambient V)
      = fun q : Ambient V => gradientCoefficient q • ((north : Ambient V) - height q • q) := by
    funext q; exact angularGradient_eq q
  rw [hfun]
  refine hG.congr_fderiv ?_
  ext v
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, zero_apply, innerSL_apply_apply, angularGradientDeriv]
  module


/-! ### The projected derivative of the gradient field -/

/-- The projected derivative of the specified ambient gradient extension, in a tangent
direction at an admissible unit point.  The `fderiv` is the genuine derivative because
`hasFDerivAt_angularGradient` supplies differentiability there. -/
lemma angularHessian_apply {p : Ambient V} (hp : ‖p‖ = 1) (h1 : -1 < height p)
    (h2 : height p < 1) {v : Ambient V} (hv : v ∈ tangentPlane p) :
    angularHessian p v =
      ((inner Real (north : Ambient V) v : Real) * gradientCoefficientDeriv p) •
          ((north : Ambient V) - height p • p)
        - (gradientCoefficient p * height p) • v := by
  have hpp : tangentProjection p p = 0 := by
    simpa using tangentProjection_smul_self hp 1
  rw [angularHessian, covariant, (hasFDerivAt_angularGradient h1 h2).fderiv,
    angularGradientDeriv_apply]
  simp only [map_sub, map_smul]
  rw [tangentProjection_eq_self hv, hpp, tangentProjection_north]
  module


/-! ### Requested theorems -/

/-- G1.  At a unit ambient point `p` with height strictly between `-1` and `1`, the actual
scalar potential `arccos ⟪north, p⟫ ^ 2 / 2` has the genuine Frechet derivative
`gradientCoefficient p • innerSL ℝ north`; the specified field `angularGradient` is genuinely
differentiable at `p`; its value lies in the tangent hyperplane; and it represents the
differential on tangent vectors.  The last conjunct is deliberately restricted to tangent
vectors: a tangent-gradient formula need not represent the ambient differential on normal
vectors, and no such claim is made. -/
theorem potential_gradient : GoalPotentialGradient V := by
  intro p hp h1 h2
  refine ⟨hasFDerivAt_angularPotential h1 h2,
    (hasFDerivAt_angularGradient h1 h2).differentiableAt,
    Submodule.smul_mem _ _ (tangentProjection_mem hp _), ?_⟩
  intro v hv
  rw [(hasFDerivAt_angularPotential h1 h2).fderiv, angularGradient_eq]
  simp only [smul_apply, innerSL_apply_apply, real_inner_smul_left,
    inner_sub_left, smul_eq_mul]
  rw [mem_tangentPlane_iff_inner.mp hv]
  ring

/-- G2.  For `0 < r < π` and unit `e` the height of `radialCurve e r` is `cos r`, which is
strictly between `-1` and `1` (proved from `sin r > 0`, so the branch denominator
`√(1 - cos r ^ 2) = sin r` is nonzero); the potential value is `r ^ 2 / 2`, since
`arccos (cos r) = r` on this branch; and the specified gradient field equals
`r • liftedFrame r e e`. -/
theorem radial_values : GoalRadialValues V := by
  intro r e hr hrpi he
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hpy := Real.sin_sq_add_cos_sq r
  have hh : height (radialCurve e r) = Real.cos r := height_radialCurve e r
  have h1 : -1 < Real.cos r := by nlinarith
  have h2 : Real.cos r < 1 := by nlinarith
  refine ⟨by rw [hh]; exact h1, by rw [hh]; exact h2, ?_, ?_⟩
  · rw [angularPotential, hh, Real.arccos_cos hr.le hrpi.le]
  · have hcoeff : gradientCoefficient (radialCurve e r) = -(r / Real.sin r) := by
      rw [gradientCoefficient, hh, Real.arccos_cos hr.le hrpi.le,
        sqrt_one_sub_cos_sq hr.le hrpi.le]
    rw [angularGradient_eq, hh, hcoeff, north_sub_smul_radialCurve r e he, smul_smul]
    congr 1
    field_simp

/-- G3.  The specified ambient gradient extension is differentiated (G1 gives its genuine
differentiability at every admissible point, so the `fderiv` in `angularHessian` is not a junk
value) and the result is projected with the 7B.2 `covariant`.  Evaluated on the actual moving
frame at `radialCurve e r`, the projected derivative is diagonal with radial eigenvalue `1` and
transverse eigenvalue `r cos r / sin r`, for every `W`, `W = 0` included.  At the equator
`r = π / 2` the transverse eigenvalue vanishes while the frame image of a nonzero transverse
vector still has norm `‖W‖`. -/
theorem angular_hessian : GoalAngularHessian V := by
  intro r e hr hrpi he W
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hpy := Real.sin_sq_add_cos_sq r
  have hp : ‖radialCurve e r‖ = 1 := norm_radialCurve e he r
  have hh : height (radialCurve e r) = Real.cos r := height_radialCurve e r
  have h1 : -1 < height (radialCurve e r) := by rw [hh]; nlinarith
  have h2 : height (radialCurve e r) < 1 := by rw [hh]; nlinarith
  have hcoeff : gradientCoefficient (radialCurve e r) = -(r / Real.sin r) := by
    rw [gradientCoefficient, hh, Real.arccos_cos hr.le hrpi.le, sqrt_one_sub_cos_sq hr.le hrpi.le]
  have hpy' : 1 - Real.cos r ^ 2 = Real.sin r ^ 2 := by nlinarith
  have hcderiv : gradientCoefficientDeriv (radialCurve e r)
      = (1 - r * Real.cos r / Real.sin r) / (Real.sin r) ^ 2 := by
    rw [gradientCoefficientDeriv, hh, Real.arccos_cos hr.le hrpi.le,
      sqrt_one_sub_cos_sq hr.le hrpi.le, hpy']
  rw [angularHessian_apply hp h1 h2 (liftedFrame_mem_tangentPlane e he r W),
    inner_north_liftedFrame, hh, hcoeff, hcderiv, north_sub_smul_radialCurve r e he]
  simp only [radialProjection, transverseProjection, sub_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
    map_add, map_sub, map_smul]
  match_scalars
  · field_simp
    ring
  · field_simp

/-- G4.  Part 1 is exactly the 7A.2 `composition_derivative` theorem for the actual
full-logarithm/product composition — not a re-proved algebraic stand-in.  Part 2 reads off its
zero scalar component and identifies the frame lift of its vector component with the Hessian
action computed in G3. -/
theorem composition_hessian : GoalCompositionHessian V := by
  intro r e hr hrpi he
  have hd := composition_derivative (V := V) r e hr hrpi he
  refine ⟨hd, fun W => ?_⟩
  rw [hd.fderiv]
  refine ⟨rfl, ?_⟩
  rw [angular_hessian (V := V) r e hr hrpi he W]
  simp [compositionDerivative]

/-- Equator check (`r = π / 2`), recorded explicitly for the return audit.  A transverse
vector `W` has vanishing Hessian action there and vanishing vector component of the actual
composition derivative, while its frame image still has norm `‖W‖`; the radial Hessian action
remains the identity. -/
lemma equator_transverse (e : V) (he : ‖e‖ = 1) (W : V) (hW : inner Real e W = 0) :
    angularHessian (radialCurve e (Real.pi / 2)) (liftedFrame (Real.pi / 2) e W) = 0 ∧
    (fderiv Real (fun Y : V => fullLog (productMap (Real.pi / 2) e Y)) 0 W).2 = 0 ∧
    ‖liftedFrame (Real.pi / 2) e W‖ = ‖W‖ ∧
    angularHessian (radialCurve e (Real.pi / 2)) (liftedFrame (Real.pi / 2) e e)
      = liftedFrame (Real.pi / 2) e e := by
  have hpi := Real.pi_pos
  have h0 : 0 < Real.pi / 2 := by linarith
  have h1 : Real.pi / 2 < Real.pi := by linarith
  have hcos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
  have hHW := angular_hessian (V := V) (Real.pi / 2) e h0 h1 he W
  have hHe := angular_hessian (V := V) (Real.pi / 2) e h0 h1 he e
  have hzeroW : angularHessian (radialCurve e (Real.pi / 2)) (liftedFrame (Real.pi / 2) e W)
      = 0 := by
    rw [hHW, hcos]
    simp [radialProjection, transverseProjection, hW]
  refine ⟨hzeroW, ?_, norm_liftedFrame e he _ W, ?_⟩
  · have hc := (composition_hessian (V := V) (Real.pi / 2) e h0 h1 he).2 W
    refine liftedFrame_injective e he (Real.pi / 2) ?_
    rw [hc.2, hzeroW, map_zero]
  · rw [hHe, hcos]
    simp [radialProjection, transverseProjection, he]

end SphericalProofRequest7B4
