import RequestProject.SphericalAmbientFrame

/-!
# Spherical repair 7B.2: the projected connection on sphere-field restrictions

This module proves the six Goal propositions stated below; their statements, and all the
definitions they are phrased with, are unchanged from the reviewed specification.  The
ambient space is the actual `L2` space `Ambient V = WithLp 2 (ℝ × V)` of 7B.1, whose genuine
Euclidean inner product, orthogonal projection `tangentProjection` onto the hyperplane
`tangentPlane p = ker (innerSL ℝ p)`, moving frame `liftedFrame` and frame derivatives were
established there and are reused here.

* `curve_tangency` (G1): for a unit `p` and `v ⟂ p` the explicitly normalized curve
  `unitCurve p v t = ‖p + t • v‖⁻¹ • (p + t • v)` passes through `p`, is unit for every real
  `t` (its inner square is `1 + t ^ 2 * ‖v‖ ^ 2 ≥ 1`, so no division by zero occurs, and the
  case `v = 0` is included), and has genuine derivative `v` at `0`.  Conversely, any curve
  staying on the unit sphere and differentiable at `0` has velocity orthogonal to `p`; that
  converse is obtained by differentiating `⟪γ t, γ t⟫ = 1`, and uses neither `unitCurve` nor
  a manifold tangent-space theorem.
* `extension_independence` (G2): two ambient fields differentiable at `p` and *equal on the
  unit sphere* (no assumption relating their ambient derivatives) have the same projected
  derivative in every tangent direction.  The proof restricts both fields to the G1 curve and
  uses the chain rule with uniqueness of derivatives.  Only global equality on the sphere is
  used; no local-germ statement and no extension theorem for abstract manifold tangent fields
  is claimed.
* `connection_laws` (G3): the projected derivative is tangent, is linear in the direction, is
  additive in the field, and satisfies the scalar Leibniz rule
  `∇_u (f • F) = (d f)(u) • F p + f p • ∇_u F`, where the unprojected value `F p` appears
  precisely because `F p` is assumed tangent.  Transparency note: the hypotheses `u, v ∈
  tangentPlane p`, `‖p‖ = 1` and `G p ∈ tangentPlane p` are not all needed by every conjunct
  (additivity and the Leibniz rule use neither the tangency of `u` and `v` nor that of `G p`;
  `‖p‖ = 1` is used for the tangency conjunct and for absorbing `F p`).  They are retained
  because the specification states them.
* `metric_compatibility` (G4): the genuine Frechet derivative of `q ↦ ⟪F q, G q⟫`, which
  exists because `F` and `G` are differentiable at `p`, equals
  `⟪∇_u F, G p⟫ + ⟪F p, ∇_u G⟫`; the right-hand side is *deduced* from the left, using that
  discarding the radial component does not change the pairing with a tangent vector.
* `bracket_and_torsion` (G5): for fields tangent along the whole sphere, the *unprojected*
  ambient bracket `d G_p (F p) - d F_p (G p)` is itself tangent — proved first, and
  independently, by differentiating `⟪q, G q⟫ = 0` and `⟪q, F q⟫ = 0` along G1 curves and
  cancelling the two symmetric metric terms — and only then is
  `∇_F G - ∇_G F = [F, G]` deduced from that tangency.
* `along_curve_and_frame` (G6): the projected derivative along a curve of the restriction of
  an ambient field agrees with the projected ambient derivative in the velocity direction
  (chain rule), and the 7B.1 moving frame is parallel: `D_t (liftedFrame t e W) = 0` for every
  unit `e`, every real `t` (endpoints and equator included, no trigonometric division) and
  every `W`.  Transparency note: the hypothesis `‖γ t‖ = 1` is not needed for the first
  conjunct, which is a pure chain-rule identity; it is retained as specified.

Scope caveat.  These are formulas about restrictions of *ambient* fields and their sphere
curves.  No bundled Mathlib manifold connection is constructed, no extension theorem for a
general local manifold tangent field is proved, and the ambient bracket is not identified with
a bundled intrinsic Lie bracket; so this package alone is not a complete Levi-Civita
identification.  Connection uniqueness and uniqueness of parallel fields are outside it, and
intrinsic path-length distance, its squared-distance Hessian and the normalized metric
recovery remain open — the chord metric inherited by the sphere is not intrinsic distance.
-/

namespace SphericalProofRequest7B2

open SphericalProofRequest7B1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

noncomputable def unitCurve (p v : Ambient V) (t : Real) : Ambient V :=
  ‖p + t • v‖⁻¹ • (p + t • v)

noncomputable def covariant (p v : Ambient V) (F : Ambient V → Ambient V) : Ambient V :=
  tangentProjection p (fderiv Real F p v)

noncomputable def ambientBracket (F G : Ambient V → Ambient V) (p : Ambient V) : Ambient V :=
  fderiv Real G p (F p) - fderiv Real F p (G p)

noncomputable def covariantAlong (gamma U : Real → Ambient V) (t : Real) : Ambient V :=
  tangentProjection (gamma t) (deriv U t)

-- G1: genuine unit curves realize the entire hyperplane, and sphere velocities lie in it.
def GoalCurveTangency (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ p : Ambient V, ‖p‖=1 →
    (∀ v : Ambient V, v ∈ tangentPlane p →
      unitCurve p v 0 = p ∧ (∀ t : Real, ‖unitCurve p v t‖=1) ∧
      HasDerivAt (unitCurve p v) v 0) ∧
    (∀ (gamma : Real → Ambient V) (v : Ambient V),
      gamma 0=p → (∀ t : Real, ‖gamma t‖=1) → HasDerivAt gamma v 0 →
      v ∈ tangentPlane p)

-- G2: equality on the sphere suffices; no equality of ambient derivatives is assumed.
def GoalExtensionIndependence (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (p v : Ambient V) (F G : Ambient V → Ambient V),
    ‖p‖=1 → v ∈ tangentPlane p → DifferentiableAt Real F p → DifferentiableAt Real G p →
    (∀ q : Ambient V, ‖q‖=1 → F q=G q) → covariant p v F = covariant p v G

-- G3: tangency, direction linearity, field additivity, and the scalar Leibniz rule.
def GoalConnectionLaws (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (p u v : Ambient V) (a : Real) (F G : Ambient V → Ambient V) (f : Ambient V → Real),
    ‖p‖=1 → u ∈ tangentPlane p → v ∈ tangentPlane p →
    F p ∈ tangentPlane p → G p ∈ tangentPlane p →
    DifferentiableAt Real F p → DifferentiableAt Real G p → DifferentiableAt Real f p →
    covariant p u F ∈ tangentPlane p ∧
    covariant p (u + a • v) F = covariant p u F + a • covariant p v F ∧
    covariant p u (fun q => F q + G q) = covariant p u F + covariant p u G ∧
    covariant p u (fun q => f q • F q) = fderiv Real f p u • F p + f p • covariant p u F

-- G4: the actual derivative of the pointwise ambient metric on tangent field values.
def GoalMetricCompatibility (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (p u : Ambient V) (F G : Ambient V → Ambient V),
    ‖p‖=1 → u ∈ tangentPlane p → F p ∈ tangentPlane p → G p ∈ tangentPlane p →
    DifferentiableAt Real F p → DifferentiableAt Real G p →
    fderiv Real (fun q => inner Real (F q) (G q)) p u =
      inner Real (covariant p u F) (G p) + inner Real (F p) (covariant p u G)

-- G5: the unprojected ambient derivative bracket is tangent and the torsion expression vanishes.
def GoalBracketAndTorsion (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (p : Ambient V) (F G : Ambient V → Ambient V),
    ‖p‖=1 → DifferentiableAt Real F p → DifferentiableAt Real G p →
    (∀ q : Ambient V, ‖q‖=1 → F q ∈ tangentPlane q) →
    (∀ q : Ambient V, ‖q‖=1 → G q ∈ tangentPlane q) →
    ambientBracket F G p ∈ tangentPlane p ∧
    covariant p (F p) G - covariant p (G p) F = ambientBracket F G p

-- G6: chain-rule agreement for restrictions to curves, and the actual existing frame.
def GoalAlongCurveAndFrame (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  (∀ (gamma : Real → Ambient V) (F : Ambient V → Ambient V) (t : Real) (v : Ambient V),
    ‖gamma t‖=1 → HasDerivAt gamma v t → DifferentiableAt Real F (gamma t) →
    covariantAlong gamma (fun s => F (gamma s)) t = covariant (gamma t) v F) ∧
  (∀ (e : V), ‖e‖=1 → ∀ (t : Real) (W : V),
    covariantAlong (radialCurve e) (fun s => liftedFrame s e W) t = 0)


/-! ### Supporting lemmas: the tangent hyperplane and its orthogonal projection -/

/-- Membership in the tangent hyperplane is orthogonality to the base point. -/
lemma mem_tangentPlane_iff_inner {p z : Ambient V} :
    z ∈ tangentPlane p ↔ (inner Real p z : Real) = 0 := Iff.rfl

/-- The explicit formula for the orthogonal projection. -/
lemma tangentProjection_apply (p z : Ambient V) :
    tangentProjection p z = z - (inner Real p z : Real) • p := rfl

/-- For a unit base point the projection lands in the tangent hyperplane. -/
lemma tangentProjection_mem {p : Ambient V} (hp : ‖p‖ = 1) (z : Ambient V) :
    tangentProjection p z ∈ tangentPlane p := by
  have hpp : (inner Real p p : Real) = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  rw [mem_tangentPlane_iff_inner, tangentProjection_apply, inner_sub_right,
    real_inner_smul_right, hpp, mul_one, sub_self]

/-- The projection fixes tangent vectors. -/
lemma tangentProjection_eq_self {p z : Ambient V} (hz : z ∈ tangentPlane p) :
    tangentProjection p z = z := by
  rw [tangentProjection_apply, mem_tangentPlane_iff_inner.mp hz, zero_smul, sub_zero]

/-- Removing the radial component does not change the pairing with a tangent vector. -/
lemma inner_tangentProjection_left (p z : Ambient V) {w : Ambient V}
    (hw : w ∈ tangentPlane p) :
    (inner Real (tangentProjection p z) w : Real) = inner Real z w := by
  have hw' : (inner Real p w : Real) = 0 := mem_tangentPlane_iff_inner.mp hw
  rw [tangentProjection_apply, inner_sub_left, real_inner_smul_left, hw', mul_zero, sub_zero]

/-- Symmetric form of `inner_tangentProjection_left`. -/
lemma inner_tangentProjection_right (p z : Ambient V) {w : Ambient V}
    (hw : w ∈ tangentPlane p) :
    (inner Real w (tangentProjection p z) : Real) = inner Real w z := by
  rw [real_inner_comm, inner_tangentProjection_left p z hw, real_inner_comm]


/-! ### Supporting lemmas: the calculus of the normalized curve `unitCurve` -/

/-- The squared norm of the affine line through a unit `p` in a perpendicular direction. -/
lemma norm_line_sq {p v : Ambient V} (hp : ‖p‖ = 1) (hv : v ∈ tangentPlane p) (t : Real) :
    ‖p + t • v‖ ^ 2 = 1 + t ^ 2 * ‖v‖ ^ 2 := by
  have hpv : (inner Real p v : Real) = 0 := mem_tangentPlane_iff_inner.mp hv
  have hvp : (inner Real v p : Real) = 0 := by rw [real_inner_comm]; exact hpv
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hpv, hvp]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hp]
  ring

/-- The affine line through a unit `p` in a perpendicular direction never meets the origin. -/
lemma line_ne_zero {p v : Ambient V} (hp : ‖p‖ = 1) (hv : v ∈ tangentPlane p) (t : Real) :
    p + t • v ≠ 0 := by
  intro h
  have h0 : ‖p + t • v‖ ^ 2 = 0 := by rw [h, norm_zero]; ring
  rw [norm_line_sq hp hv t] at h0
  nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg ‖v‖)]

/-- The normalizing factor as an explicit real function of the parameter. -/
lemma norm_line_eq_sqrt {p v : Ambient V} (hp : ‖p‖ = 1) (hv : v ∈ tangentPlane p) (t : Real) :
    ‖p + t • v‖ = Real.sqrt (1 + t ^ 2 * ‖v‖ ^ 2) := by
  rw [← norm_line_sq hp hv t, Real.sqrt_sq (norm_nonneg _)]

/-- The normalized curve stays on the unit sphere for every real parameter. -/
lemma norm_unitCurve {p v : Ambient V} (hp : ‖p‖ = 1) (hv : v ∈ tangentPlane p) (t : Real) :
    ‖unitCurve p v t‖ = 1 := by
  have hnn : ‖p + t • v‖ ≠ 0 := norm_ne_zero_iff.mpr (line_ne_zero hp hv t)
  rw [unitCurve, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnn]

/-- The normalized curve starts at `p`. -/
lemma unitCurve_zero (p v : Ambient V) (hp : ‖p‖ = 1) : unitCurve p v 0 = p := by
  rw [unitCurve, zero_smul, add_zero, hp, inv_one, one_smul]

/-- The normalizing factor has vanishing derivative at the parameter `0`. -/
lemma hasDerivAt_norm_line_inv {p v : Ambient V} (hp : ‖p‖ = 1) (hv : v ∈ tangentPlane p) :
    HasDerivAt (fun t : Real => ‖p + t • v‖⁻¹) 0 0 := by
  have hfun : (fun t : Real => ‖p + t • v‖⁻¹)
      = fun t : Real => (Real.sqrt (1 + t ^ 2 * ‖v‖ ^ 2))⁻¹ := by
    funext t; rw [norm_line_eq_sqrt hp hv t]
  have hval : (1 : Real) + (0 : Real) ^ 2 * ‖v‖ ^ 2 = 1 := by ring
  have hu : HasDerivAt (fun t : Real => 1 + t ^ 2 * ‖v‖ ^ 2) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : Real)).mul_const (‖v‖ ^ 2)).const_add 1
  have hs : HasDerivAt (fun t : Real => Real.sqrt (1 + t ^ 2 * ‖v‖ ^ 2)) 0 0 := by
    simpa using hu.sqrt (by rw [hval]; norm_num)
  have hne : Real.sqrt (1 + (0 : Real) ^ 2 * ‖v‖ ^ 2) ≠ 0 := by
    rw [hval, Real.sqrt_one]; norm_num
  have hinv := hs.inv hne
  have hzero : (-(0 : Real) / (Real.sqrt (1 + (0 : Real) ^ 2 * ‖v‖ ^ 2)) ^ 2) = 0 := by
    rw [hval, Real.sqrt_one]; norm_num
  rw [hzero] at hinv
  rw [hfun]
  exact hinv

/-- The normalized curve has genuine derivative `v` at the parameter `0`. -/
lemma hasDerivAt_unitCurve {p v : Ambient V} (hp : ‖p‖ = 1) (hv : v ∈ tangentPlane p) :
    HasDerivAt (unitCurve p v) v 0 := by
  have hline : HasDerivAt (fun t : Real => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : Real)).smul_const v).const_add p
  have h := (hasDerivAt_norm_line_inv hp hv).smul hline
  have h' : HasDerivAt (fun t : Real => ‖p + t • v‖⁻¹ • (p + t • v)) v 0 := by
    refine h.congr_deriv ?_
    simp [hp]
  exact h'

/-- The chain rule for the restriction of an ambient field to a curve. -/
lemma hasDerivAt_comp_curve {p v : Ambient V} {F : Ambient V → Ambient V} {c : Real → Ambient V}
    {t : Real} (hF : DifferentiableAt Real F p) (hc0 : c t = p) (hc : HasDerivAt c v t) :
    HasDerivAt (fun s : Real => F (c s)) (fderiv Real F p v) t := by
  have hF' : HasFDerivAt F (fderiv Real F p) (c t) := by rw [hc0]; exact hF.hasFDerivAt
  exact hF'.comp_hasDerivAt t hc


/-! ### Requested theorems -/

/-- G1.  For a unit `p`, every vector `v` of the hyperplane `tangentPlane p` is realized as
the velocity at `0` of the explicit unit-sphere curve `unitCurve p v` through `p` (the case
`v = 0` included; the normalizing factor never vanishes since `‖p + t • v‖ ^ 2 =
1 + t ^ 2 * ‖v‖ ^ 2`).  Conversely, every curve lying on the unit sphere and differentiable at
`0` with `γ 0 = p` has velocity in that hyperplane; this converse differentiates
`⟪γ t, γ t⟫ = 1` and uses neither `unitCurve` nor any manifold tangent-space theorem. -/
theorem curve_tangency : GoalCurveTangency V := by
  intro p hp
  refine ⟨fun v hv => ⟨unitCurve_zero p v hp, fun t => norm_unitCurve hp hv t,
    hasDerivAt_unitCurve hp hv⟩, ?_⟩
  intro gamma v h0 hunit hd
  have hconst : (fun t : Real => (inner Real (gamma t) (gamma t) : Real))
      = fun _ => (1 : Real) := by
    funext t; rw [real_inner_self_eq_norm_sq, hunit t, one_pow]
  have hd1 : HasDerivAt (fun t : Real => (inner Real (gamma t) (gamma t) : Real))
      ((inner Real (gamma 0) v : Real) + inner Real v (gamma 0)) 0 := hd.inner Real hd
  have hd2 : HasDerivAt (fun t : Real => (inner Real (gamma t) (gamma t) : Real)) 0 0 := by
    rw [hconst]; exact hasDerivAt_const 0 1
  have hsum : (inner Real (gamma 0) v : Real) + inner Real v (gamma 0) = 0 := hd1.unique hd2
  rw [h0] at hsum
  have hcomm : (inner Real v p : Real) = inner Real p v := real_inner_comm p v
  rw [mem_tangentPlane_iff_inner]
  linarith

/-- G2.  Two ambient fields differentiable at a unit `p` and agreeing at every unit point have
the same projected derivative in every tangent direction.  No relation between their ambient
derivatives is assumed: both are restricted to the G1 curve, where the chain rule and
uniqueness of derivatives force the two directional derivatives to agree.  Only equality on
the whole sphere is used; this is not a local-germ or manifold extension statement. -/
theorem extension_independence : GoalExtensionIndependence V := by
  intro p v F G hp hv hF hG hFG
  have hc : HasDerivAt (unitCurve p v) v 0 := hasDerivAt_unitCurve hp hv
  have hc0 : unitCurve p v 0 = p := unitCurve_zero p v hp
  have hFd : HasDerivAt (fun t : Real => F (unitCurve p v t)) (fderiv Real F p v) 0 :=
    hasDerivAt_comp_curve hF hc0 hc
  have hGd : HasDerivAt (fun t : Real => G (unitCurve p v t)) (fderiv Real G p v) 0 :=
    hasDerivAt_comp_curve hG hc0 hc
  have heq : (fun t : Real => F (unitCurve p v t)) = fun t : Real => G (unitCurve p v t) := by
    funext t; exact hFG _ (norm_unitCurve hp hv t)
  rw [heq] at hFd
  rw [covariant, covariant, hFd.unique hGd]

/-- G3.  The projected derivative takes values in the tangent hyperplane, is linear in the
direction, is additive in the field, and obeys the scalar Leibniz rule with the unprojected
value `F p` (which is legitimate because `F p` is assumed tangent).  Transparency note: the
tangency hypotheses on `u` and `v` are not used at all, `G p ∈ tangentPlane p` is used by no
conjunct, and `‖p‖ = 1` is needed only for the first (tangency) conjunct; those hypotheses are
retained because the specification states them. -/
theorem connection_laws : GoalConnectionLaws V := by
  intro p u v a F G f hp _hu _hv hFp _hGp hF hG hf
  refine ⟨tangentProjection_mem hp _, ?_, ?_, ?_⟩
  · rw [covariant, covariant, covariant, map_add, map_smul, map_add, map_smul]
  · rw [covariant, covariant, covariant, fderiv_fun_add hF hG]
    simp
  · rw [covariant, fderiv_fun_smul hf hF]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
    rw [tangentProjection_eq_self hFp, covariant, add_comm]

/-- G4.  Since `F` and `G` are differentiable at `p`, the pointwise ambient inner product
`q ↦ ⟪F q, G q⟫` is genuinely differentiable at `p`, and its actual derivative in the
direction `u` equals `⟪∇_u F, G p⟫ + ⟪F p, ∇_u G⟫`.  The right-hand side is deduced from the
left, using that discarding the radial component of a vector does not change its pairing with
the tangent values `F p` and `G p`.  Transparency note: the tangency of `u` is not needed. -/
theorem metric_compatibility : GoalMetricCompatibility V := by
  intro p u F G hp _hu hFp hGp hF hG
  rw [(hF.hasFDerivAt.inner Real hG.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply]
  rw [covariant, covariant, inner_tangentProjection_left p _ hGp,
    inner_tangentProjection_right p _ hFp]
  exact add_comm _ _

/-- G5.  If `F` and `G` are tangent at every unit point and differentiable at a unit `p`, the
*unprojected* ambient bracket `d G_p (F p) - d F_p (G p)` is tangent at `p`.  This first
conjunct is proved on its own, by differentiating `⟪q, G q⟫ = 0` along the G1 curve with
velocity `F p` and `⟪q, F q⟫ = 0` along the one with velocity `G p`; the two metric terms
`⟪F p, G p⟫` and `⟪G p, F p⟫` cancel by symmetry.  Only then is
`∇_{F p} G - ∇_{G p} F = [F, G]` deduced, by applying the projection to the already tangent
bracket. -/
theorem bracket_and_torsion : GoalBracketAndTorsion V := by
  intro p F G hp hF hG hFt hGt
  have hFp : F p ∈ tangentPlane p := hFt p hp
  have hGp : G p ∈ tangentPlane p := hGt p hp
  have key : ∀ (X Y : Ambient V → Ambient V), DifferentiableAt Real Y p →
      (∀ q : Ambient V, ‖q‖ = 1 → Y q ∈ tangentPlane q) → X p ∈ tangentPlane p →
      (inner Real (X p) (Y p) : Real) + inner Real p (fderiv Real Y p (X p)) = 0 := by
    intro X Y hY hYt hXp
    set c : Real → Ambient V := unitCurve p (X p)
    have hc : HasDerivAt c (X p) 0 := hasDerivAt_unitCurve hp hXp
    have hc0 : c 0 = p := unitCurve_zero p (X p) hp
    have hcu : ∀ t : Real, ‖c t‖ = 1 := fun t => norm_unitCurve hp hXp t
    have hYc : HasDerivAt (fun t : Real => Y (c t)) (fderiv Real Y p (X p)) 0 :=
      hasDerivAt_comp_curve hY hc0 hc
    have hd1 : HasDerivAt (fun t : Real => (inner Real (c t) (Y (c t)) : Real))
        ((inner Real (c 0) (fderiv Real Y p (X p)) : Real) + inner Real (X p) (Y (c 0))) 0 :=
      hc.inner Real hYc
    have hzero : (fun t : Real => (inner Real (c t) (Y (c t)) : Real)) = fun _ => (0 : Real) := by
      funext t
      exact mem_tangentPlane_iff_inner.mp (hYt (c t) (hcu t))
    have hd2 : HasDerivAt (fun t : Real => (inner Real (c t) (Y (c t)) : Real)) 0 0 := by
      rw [hzero]; exact hasDerivAt_const 0 0
    have hsum := hd1.unique hd2
    rw [hc0] at hsum
    linarith
  have h1 := key F G hG hGt hFp
  have h2 := key G F hF hFt hGp
  have hcomm : (inner Real (F p) (G p) : Real) = inner Real (G p) (F p) :=
    real_inner_comm (G p) (F p)
  have htan : ambientBracket F G p ∈ tangentPlane p := by
    rw [mem_tangentPlane_iff_inner, ambientBracket, inner_sub_right]
    linarith
  refine ⟨htan, ?_⟩
  have hsplit : covariant p (F p) G - covariant p (G p) F
      = tangentProjection p (ambientBracket F G p) := by
    rw [covariant, covariant, ambientBracket, map_sub]
  rw [hsplit, tangentProjection_eq_self htan]

/-- G6.  First conjunct: the projected derivative along a curve of the restriction of an
ambient field agrees with the projected ambient derivative in the velocity direction; this is
the chain rule together with uniqueness of derivatives, and the hypothesis `‖γ t‖ = 1` is not
needed for it (it is retained as specified).  Second conjunct: the 7B.1 moving frame is
parallel along the radial curve, `D_t (liftedFrame t e W) = 0`, for every unit `e`, every real
`t` (including the endpoints `0`, `π` and the equator `π / 2`) and every `W`; no sine or
cosine is ever inverted. -/
theorem along_curve_and_frame : GoalAlongCurveAndFrame V := by
  constructor
  · intro gamma F t v _hgamma hd hF
    have hcomp : HasDerivAt (fun s : Real => F (gamma s)) (fderiv Real F (gamma t) v) t :=
      hasDerivAt_comp_curve hF rfl hd
    rw [covariantAlong, hcomp.deriv, covariant]
  · intro e he t W
    rw [covariantAlong, (hasDerivAt_liftedFrame e t W).deriv]
    exact tangentProjection_smul_self (norm_radialCurve e he t) _

end SphericalProofRequest7B2
