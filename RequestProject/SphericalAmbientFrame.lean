import RequestProject.SphericalExpFactorization
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Spherical repair 7B.1: L2 ambient geometry and the moving frame

This module proves the five Goal propositions stated below; their statements, and all the
definitions they are phrased with, are unchanged from the reviewed specification.

* `ambient_metric` (G1): `Ambient V = WithLp 2 (ℝ × V)` carries the actual Euclidean inner
  product — `⟪toAmbient x, toAmbient y⟫ = x.1 * y.1 + ⟪x.2, y.2⟫`, `‖toAmbient x‖ ^ 2 =
  euclideanSquare x` — and `radialCurve e t` is a unit vector for every real `t` whenever
  `‖e‖ = 1`.  Nothing is asserted about the ordinary product maximum norm.
* `level_and_projection` (G2): at a unit `p` the squared ambient norm has Frechet derivative
  `2 • innerSL ℝ p`, whose kernel is `tangentPlane p` and whose value at `p` is `2`; and
  `tangentProjection p` lands in `tangentPlane p` with orthogonal remainder, the two
  properties that characterize the orthogonal projection onto that hyperplane.
* `frame_isometry` (G3): `liftedFrame t e` is the underlying map of an onto
  `LinearIsometryEquiv` from `V` to `tangentPlane (radialCurve e t)`.  No finite dimension and
  no completeness hypothesis is used; the inverse is the explicit map built from the radial
  coefficient `-sin t * z.1 + cos t * ⟪e, z.2⟫` and the perpendicular part of `z.2`, so no
  trigonometric factor is ever inverted and the parameters with `sin t = 0` or `cos t = 0`
  are covered.
* `projected_frame_derivative` (G4): `radialCurve e` has velocity `liftedFrame t e e`, the
  frame satisfies `(d/dt) (liftedFrame t e W) = -⟪e, W⟫ • radialCurve e t`, and that
  derivative is annihilated by `tangentProjection (radialCurve e t)`.  All statements hold
  for every real `t`, including `0`, `π / 2`, `π` and negative values, and for every `W`
  (including `W = 0`).
* `lifted_derivatives` (G5): the actual 7A.3 exponential derivative and 7A.1 product
  derivative, composed with `toAmbient`, have `L2` codomain derivatives
  `liftedFrame r e ∘ jacobiMap r e` and `liftedFrame r e ∘ compressionMap r e`, on the branch
  `0 < r < π` retained from those earlier statements.

Scope caveat.  `tangentPlane p` is the explicit orthogonal hyperplane `ker (innerSL ℝ p)`; it
is *not* identified here with a bundled Mathlib manifold tangent space.  No connection is
constructed, and no metric compatibility or torsion-freeness is proved: the vanishing of the
projected derivative of this explicit frame is extrinsic evidence for such a later bridge,
not a proof that an independently defined Levi-Civita connection has been recovered.  The
product map of G5 need not stay on the sphere; only its first variation is related to the
hyperplane.  Intrinsic path-length distance, its squared-distance Hessian and the normalized
metric recovery remain open, and the chord distance inherited by the sphere subtype is not
used as a geodesic distance anywhere.
-/

namespace SphericalProofRequest7B1

open SphericalProofRequest7A1 SphericalProofRequest7A2 SphericalProofRequest7A3

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

abbrev Ambient (V : Type*) := WithLp 2 (Real × V)

noncomputable def toAmbient : (Real × V) →L[Real] Ambient V :=
  (WithLp.prodContinuousLinearEquiv 2 Real Real V).symm.toContinuousLinearMap

noncomputable def radialCurve (e : V) (t : Real) : Ambient V :=
  toAmbient (basePoint t e)

noncomputable def liftedFrame (t : Real) (e : V) : V →L[Real] Ambient V :=
  (toAmbient (V:=V)).comp (coordinateLift t e)

noncomputable def tangentPlane (p : Ambient V) : Submodule Real (Ambient V) :=
  (innerSL Real p).ker

noncomputable def tangentProjection (p : Ambient V) : Ambient V →L[Real] Ambient V :=
  ContinuousLinearMap.id Real (Ambient V) - (innerSL Real p).smulRight p

-- G1: actual Euclidean inner product, not the ordinary product maximum norm.
def GoalAmbientMetric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  (∀ x y : Real × V, inner Real (toAmbient x) (toAmbient y) = x.1*y.1 + inner Real x.2 y.2) ∧
  (∀ x : Real × V, ‖toAmbient x‖^2 = euclideanSquare x) ∧
  (∀ (e : V), ‖e‖=1 → ∀ t : Real, ‖radialCurve e t‖=1)

-- G2: regular level-set differential and the characterizing orthogonal-projection properties.
def GoalLevelAndProjection (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ p : Ambient V, ‖p‖=1 →
    HasFDerivAt (fun q : Ambient V => ‖q‖^2) (2 • innerSL Real p) p ∧
    tangentPlane p = (2 • innerSL Real p).ker ∧
    (2 • innerSL Real p) p = 2 ∧
    (∀ z : Ambient V, tangentProjection p z ∈ tangentPlane p ∧
      ∀ w : Ambient V, w ∈ tangentPlane p → inner Real (z-tangentProjection p z) w = 0)

-- G3: an onto linear isometry into the actual L2 orthogonal hyperplane.
def GoalFrameIsometry (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (e : V), ‖e‖=1 → ∀ t : Real,
    ∃ T : V ≃ₗᵢ[Real] ↥(tangentPlane (radialCurve e t)),
      ∀ W : V, (T W : Ambient V) = liftedFrame t e W

-- G4: differentiate the actual moving frame and prove its projected derivative vanishes.
def GoalProjectedFrameDerivative (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (e : V), ‖e‖=1 → ∀ (t : Real) (W : V),
    HasDerivAt (radialCurve e) (liftedFrame t e e) t ∧
    HasDerivAt (fun u : Real => liftedFrame u e W) (-(inner Real e W) • radialCurve e t) t ∧
    tangentProjection (radialCurve e t) (-(inner Real e W) • radialCurve e t) = 0

-- G5: move the previously proved actual derivatives into the L2 geometry.
def GoalLiftedDerivatives (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0<r → r<Real.pi → ‖e‖=1 →
    HasFDerivAt (fun X : V => toAmbient (expCoordinates X))
      ((liftedFrame r e).comp (jacobiMap r e)) (r • e) ∧
    HasFDerivAt (fun Y : V => toAmbient (productMap r e Y))
      ((liftedFrame r e).comp (compressionMap r e)) 0



/-! ### Supporting lemmas: the L2 ambient geometry -/

/-- `toAmbient` is the tautological repackaging of a pair as an `L2` element. -/
lemma toAmbient_apply (x : Real × V) : (toAmbient x : Ambient V) = WithLp.toLp 2 x := by
  simp [toAmbient]

/-- The actual Euclidean inner product of two ambient vectors. -/
lemma inner_toAmbient (x y : Real × V) :
    inner Real (toAmbient x) (toAmbient y) = x.1 * y.1 + inner Real x.2 y.2 := by
  rw [toAmbient_apply, toAmbient_apply, WithLp.prod_inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- The actual Euclidean square of the norm of an ambient vector. -/
lemma norm_toAmbient_sq (x : Real × V) : ‖toAmbient x‖ ^ 2 = euclideanSquare x := by
  rw [← real_inner_self_eq_norm_sq, inner_toAmbient]
  simp [euclideanSquare, sq]

/-- A nonnegative real number is determined by its square. -/
private lemma eq_of_sq_eq_sq_of_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := (sq_eq_sq₀ ha hb).mp h

/-- For a unit vector the self inner product is one. -/
private lemma inner_self_unit {e : V} (he : ‖e‖ = 1) : (inner Real e e : Real) = 1 := by
  rw [real_inner_self_eq_norm_sq, he, one_pow]

/-- Expansion of `‖a • e + W‖ ^ 2` for a unit vector `e`. -/
private lemma norm_smul_add_sq {a : Real} {e W : V} (he : ‖e‖ = 1) :
    ‖a • e + W‖ ^ 2 = a ^ 2 + 2 * a * inner Real e W + ‖W‖ ^ 2 := by
  have hee : (inner Real e e : Real) = 1 := inner_self_unit he
  rw [← real_inner_self_eq_norm_sq (x := a • e + W)]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hee,
    real_inner_comm W e]
  rw [real_inner_self_eq_norm_sq]
  ring

/-- The explicit coordinate description of the moving frame. -/
lemma liftedFrame_apply (t : Real) (e W : V) :
    liftedFrame t e W =
      toAmbient (-Real.sin t * inner Real e W,
        (Real.cos t * inner Real e W - inner Real e W) • e + W) := by
  refine congrArg (toAmbient (V := V)) (Prod.ext rfl ?_)
  simp [coordinateLift, radialProjection, transverseProjection]
  module

/-- The radial curve in ambient coordinates. -/
lemma radialCurve_apply (e : V) (t : Real) :
    radialCurve e t = toAmbient (Real.cos t, Real.sin t • e) := rfl

/-- The radial curve is a unit vector of the actual `L2` ambient space. -/
lemma norm_radialCurve (e : V) (he : ‖e‖ = 1) (t : Real) : ‖radialCurve e t‖ = 1 := by
  refine eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) zero_le_one ?_
  rw [radialCurve_apply, norm_toAmbient_sq]
  simp [euclideanSquare, norm_smul, he, sq_abs, Real.norm_eq_abs]


/-! ### Derivatives of the radial curve and of the moving frame -/

/-- The frame applied to the radial direction is the velocity vector of the radial curve. -/
lemma liftedFrame_self (e : V) (he : ‖e‖ = 1) (t : Real) :
    liftedFrame t e e = toAmbient (-Real.sin t, Real.cos t • e) := by
  rw [liftedFrame_apply, inner_self_unit he]
  refine congrArg (toAmbient (V := V)) (Prod.ext ?_ ?_)
  · exact mul_one _
  · show (Real.cos t * 1 - 1) • e + e = Real.cos t • e
    module

/-- The radial curve is differentiable with velocity the frame applied to `e`. -/
lemma hasDerivAt_radialCurve (e : V) (he : ‖e‖ = 1) (t : Real) :
    HasDerivAt (radialCurve e) (liftedFrame t e e) t := by
  have hpair : HasDerivAt (fun u : Real => ((Real.cos u : Real), Real.sin u • e))
      ((-Real.sin t), Real.cos t • e) t :=
    (Real.hasDerivAt_cos t).prodMk ((Real.hasDerivAt_sin t).smul_const e)
  have h := (toAmbient (V := V)).hasFDerivAt.comp_hasDerivAt t hpair
  rw [liftedFrame_self e he t]
  exact h

/-- The moving frame is differentiable in the parameter, with derivative pointing along the
radial direction; no unit hypothesis is needed for this identity. -/
lemma hasDerivAt_liftedFrame (e : V) (t : Real) (W : V) :
    HasDerivAt (fun u : Real => liftedFrame u e W)
      (-(inner Real e W) • radialCurve e t) t := by
  set a : Real := inner Real e W with ha
  have hfun : (fun u : Real => liftedFrame u e W) =
      fun u : Real => toAmbient (-Real.sin u * a, (Real.cos u * a - a) • e + W) := by
    funext u; rw [liftedFrame_apply]
  have hpair : HasDerivAt
      (fun u : Real => ((-Real.sin u * a : Real), (Real.cos u * a - a) • e + W))
      ((-Real.cos t * a), ((-Real.sin t) * a) • e) t := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using ((Real.hasDerivAt_sin t).neg.mul_const a)
    · simpa using ((((Real.hasDerivAt_cos t).mul_const a).sub_const a).smul_const e).add_const W
  have h := (toAmbient (V := V)).hasFDerivAt.comp_hasDerivAt t hpair
  rw [hfun]
  refine h.congr_deriv ?_
  rw [radialCurve_apply, ← map_smul]
  refine congrArg (toAmbient (V := V)) (Prod.ext ?_ ?_)
  · show -Real.cos t * a = -a * Real.cos t
    ring
  · show ((-Real.sin t) * a) • e = -a • (Real.sin t • e)
    module

/-- The radial component of the frame derivative is annihilated by the projection. -/
lemma tangentProjection_smul_self {p : Ambient V} (hp : ‖p‖ = 1) (c : Real) :
    tangentProjection p (c • p) = 0 := by
  simp [tangentProjection, hp]


/-! ### The moving frame as a linear isometry onto the tangent hyperplane -/

/-- Every ambient vector is the lift of its pair of coordinates. -/
lemma toAmbient_ofLp (z : Ambient V) : toAmbient (WithLp.ofLp z) = z := by
  rw [toAmbient_apply]

/-- Membership in the tangent hyperplane, in coordinates. -/
lemma mem_tangentPlane_iff (e : V) (t : Real) (z : Ambient V) :
    z ∈ tangentPlane (radialCurve e t) ↔
      Real.cos t * (WithLp.ofLp z).1 + Real.sin t * inner Real e (WithLp.ofLp z).2 = 0 := by
  rw [← toAmbient_ofLp z]
  simp only [tangentPlane, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
    radialCurve_apply, inner_toAmbient, real_inner_smul_left]
  rw [toAmbient_ofLp]

/-- The frame vector lies in the tangent hyperplane at the corresponding point of the
radial curve, for every real `t`. -/
lemma liftedFrame_mem_tangentPlane (e : V) (he : ‖e‖ = 1) (t : Real) (W : V) :
    liftedFrame t e W ∈ tangentPlane (radialCurve e t) := by
  have hee : (inner Real e e : Real) = 1 := inner_self_unit he
  rw [mem_tangentPlane_iff, liftedFrame_apply]
  simp only [toAmbient_apply]
  show Real.cos t * (-Real.sin t * inner Real e W) +
    Real.sin t * inner Real e ((Real.cos t * inner Real e W - inner Real e W) • e + W) = 0
  rw [inner_add_right, real_inner_smul_right, hee]
  ring

/-- The moving frame preserves norms: it is an isometry onto its image, for every real `t`. -/
lemma norm_liftedFrame (e : V) (he : ‖e‖ = 1) (t : Real) (W : V) :
    ‖liftedFrame t e W‖ = ‖W‖ := by
  refine eq_of_sq_eq_sq_of_nonneg (norm_nonneg _) (norm_nonneg _) ?_
  rw [liftedFrame_apply, norm_toAmbient_sq]
  simp only [euclideanSquare]
  rw [norm_smul_add_sq he]
  have hpy := Real.sin_sq_add_cos_sq t
  linear_combination (inner Real e W : Real) ^ 2 * hpy

/-- The moving frame is onto the tangent hyperplane: the explicit preimage uses the radial
coefficient `-sin t * z.1 + cos t * ⟪e, z.2⟫` together with the perpendicular part of the
vector coordinate.  No trigonometric denominator occurs, so `sin t = 0` and `cos t = 0` are
covered. -/
lemma liftedFrame_surjective (e : V) (he : ‖e‖ = 1) (t : Real) {z : Ambient V}
    (hz : z ∈ tangentPlane (radialCurve e t)) : ∃ W : V, liftedFrame t e W = z := by
  have hee : (inner Real e e : Real) = 1 := inner_self_unit he
  set s : Real := (WithLp.ofLp z).1 with hs
  set v : V := (WithLp.ofLp z).2 with hv
  set m : Real := inner Real e v with hm
  have hcon : Real.cos t * s + Real.sin t * m = 0 := (mem_tangentPlane_iff e t z).mp hz
  have hpy := Real.sin_sq_add_cos_sq t
  set c : Real := -Real.sin t * s + Real.cos t * m with hc
  refine ⟨c • e + (v - m • e), ?_⟩
  have hinner : (inner Real e (c • e + (v - m • e)) : Real) = c := by
    rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right, hee, ← hm]
    ring
  have hscal : -Real.sin t * c = s := by
    rw [hc]; linear_combination (-Real.cos t) * hcon + s * hpy
  have hcm : Real.cos t * c - m = 0 := by
    rw [hc]; linear_combination (-Real.sin t) * hcon + m * hpy
  rw [liftedFrame_apply, hinner, hscal]
  rw [← toAmbient_ofLp z]
  refine congrArg (toAmbient (V := V)) (Prod.ext rfl ?_)
  show (Real.cos t * c - c) • e + (c • e + (v - m • e)) = v
  have hrw : (Real.cos t * c - c) • e + (c • e + (v - m • e))
      = (Real.cos t * c - m) • e + v := by module
  rw [hrw, hcm, zero_smul, zero_add]

/-- The moving frame packaged as a linear isometry from `V` into the tangent hyperplane. -/
noncomputable def frameLinearIsometry (e : V) (he : ‖e‖ = 1) (t : Real) :
    V →ₗᵢ[Real] ↥(tangentPlane (radialCurve e t)) where
  toLinearMap := LinearMap.codRestrict _ (liftedFrame t e).toLinearMap
    (liftedFrame_mem_tangentPlane e he t)
  norm_map' := fun W => by
    simpa [Submodule.coe_norm] using norm_liftedFrame e he t W

/-- G1.  The ambient space carries the actual Euclidean (`L2`) inner product: the inner
product of two lifted pairs is the sum of the scalar and vector inner products, the squared
norm is `euclideanSquare`, and the radial curve of a unit vector lies on the unit sphere for
every real `t` (no restriction on `t`). -/
theorem ambient_metric : GoalAmbientMetric V :=
  ⟨inner_toAmbient, norm_toAmbient_sq, fun e he t => norm_radialCurve e he t⟩
/-- G2.  At a unit ambient vector `p` the squared norm has Frechet derivative
`2 • innerSL ℝ p`, whose kernel is exactly `tangentPlane p` and whose value at `p` is `2`
(so the unit sphere is a regular level set at `p`).  Moreover `tangentProjection p z` lies in
`tangentPlane p` and the discarded part `z - tangentProjection p z` is orthogonal to the whole
of `tangentPlane p`; these two properties characterize the orthogonal projection. -/
theorem level_and_projection : GoalLevelAndProjection V := by
  intro p hp
  have hpp : (inner Real p p : Real) = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  refine ⟨(hasStrictFDerivAt_norm_sq p).hasFDerivAt, ?_, ?_, ?_⟩
  · ext z
    simp only [tangentPlane, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, smul_apply,
      innerSL_apply_apply, nsmul_eq_mul]
    constructor
    · intro h; rw [h, mul_zero]
    · intro h; simpa using h
  · simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, hpp, mul_one, Nat.cast_ofNat]
  · intro z
    have hz : z - tangentProjection p z = (inner Real p z : Real) • p := by
      simp [tangentProjection]
    refine ⟨?_, ?_⟩
    · simp only [tangentPlane, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
        innerSL_apply_apply, tangentProjection,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, sub_apply,
        inner_sub_right,
        real_inner_smul_right, hpp]
      ring
    · intro w hw
      have hw' : (inner Real p w : Real) = 0 := by
        simpa [tangentPlane] using hw
      rw [hz, real_inner_smul_left, hw', mul_zero]
/-- G3.  For a unit vector `e` and every real `t`, the moving frame is an onto linear isometry
equivalence from `V` to the tangent hyperplane at `radialCurve e t`, with underlying map
exactly `liftedFrame t e`.  No finite dimensionality or completeness is assumed, and the
inverse is explicit, so the degenerate parameters `sin t = 0` and `cos t = 0` are included. -/
theorem frame_isometry : GoalFrameIsometry V := by
  intro e he t
  have hsurj : Function.Surjective (frameLinearIsometry e he t) := by
    rintro ⟨z, hz⟩
    obtain ⟨W, hW⟩ := liftedFrame_surjective e he t hz
    exact ⟨W, Subtype.ext hW⟩
  refine ⟨LinearIsometryEquiv.ofSurjective (frameLinearIsometry e he t) hsurj, fun W => ?_⟩
  rw [LinearIsometryEquiv.coe_ofSurjective]
  rfl
/-- G4.  For a unit vector `e` and every real `t` (including `t = 0`, `π / 2`, `π` and
negative `t`) the radial curve has velocity `liftedFrame t e e`, the moving frame has
`t`-derivative `-⟪e, W⟫ • radialCurve e t`, and that derivative is purely radial, so its
orthogonal projection onto the tangent plane vanishes.  This is an extrinsic
projected-derivative statement about the explicit frame, not a statement about an
independently defined Levi-Civita connection. -/
theorem projected_frame_derivative : GoalProjectedFrameDerivative V := by
  intro e he t W
  exact ⟨hasDerivAt_radialCurve e he t, hasDerivAt_liftedFrame e t W,
    tangentProjection_smul_self (norm_radialCurve e he t) _⟩
/-- G5.  The previously proved coordinate derivatives of the sinc exponential (7A.3) and of
the spin-factor product map (7A.1) transported into the `L2` ambient space: their Frechet
derivatives factor as the moving frame composed with the Jacobi map, respectively with the
compression map.  Only the first variation is related to the hyperplane; the product map
itself is not claimed to stay on the sphere. -/
theorem lifted_derivatives : GoalLiftedDerivatives V := by
  intro r e hr hrpi he
  obtain ⟨hexp, hprod, -⟩ := coordinate_identities r e hr hrpi he
  constructor
  · have hd : HasFDerivAt (fun X : V => toAmbient (expCoordinates X))
        ((toAmbient (V := V)).comp (expDerivative r e)) (r • e) :=
      (toAmbient (V := V)).hasFDerivAt.comp (r • e) (exp_derivative r e hr hrpi he)
    refine hd.congr_fderiv ?_
    rw [hexp, liftedFrame, ContinuousLinearMap.comp_assoc]
  · have hd : HasFDerivAt (fun Y : V => toAmbient (productMap r e Y))
        ((toAmbient (V := V)).comp (productDerivative r e)) 0 :=
      (toAmbient (V := V)).hasFDerivAt.comp 0 (product_derivative r e hr hrpi he)
    refine hd.congr_fderiv ?_
    rw [hprod, liftedFrame, ContinuousLinearMap.comp_assoc]

end SphericalProofRequest7B1
