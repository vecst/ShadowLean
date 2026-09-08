import RequestProject.SphericalProjectedConnection

/-!
# Spherical repair 7B.3: uniqueness and radial parallel transport

This module proves the four Goal propositions stated below; their statements, and all the
definitions they are phrased with, are unchanged from the reviewed specification.  The
setting is the one of 7B.1 and 7B.2: the actual `L2` ambient space `Ambient V =
WithLp 2 (ℝ × V)`, the explicit orthogonal hyperplane `tangentPlane p = ker (innerSL ℝ p)`
with its projection `tangentProjection p`, the moving frame `liftedFrame t e` and the
projected derivative along a curve `covariantAlong gamma U t = tangentProjection (gamma t)
(deriv U t)`.

`IsParallelAlong gamma U` asks for the three genuine conditions: `U t` is tangent at
`gamma t` for every real `t`, `U` is differentiable at every real `t`, and the actual
projected derivative `covariantAlong gamma U t` vanishes for every real `t`.  The
differentiability requirement is essential: it prevents the junk value of `deriv` at a
non-differentiability point from producing spurious "parallel" fields.

* `along_metric` (G1): if `U t` and `Z t` are tangent at `gamma t` and both fields are
  differentiable at `t`, then `s ↦ ⟪U s, Z s⟫` has the genuine derivative
  `⟪D_t U, Z t⟫ + ⟪U t, D_t Z⟫` at `t`.  The proof differentiates the actual inner product
  and then replaces the ambient derivatives by their projections, which is legitimate because
  discarding the radial component does not change the pairing with a tangent vector
  (7B.2 `inner_tangentProjection_left` / `inner_tangentProjection_right`).  The hypothesis
  `‖gamma t‖ = 1` is not needed for this identity; it is retained as specified.
* `parallel_uniqueness` (G2): for a unit-valued `gamma` and two fields parallel on all of `ℝ`,
  the pairing `⟪U t, Z t⟫` is constant in `t`, and if `U s = Z s` for one parameter then
  `U = Z` everywhere.  Constancy is G1 plus the real mean-value theorem
  (`is_const_of_deriv_eq_zero`); the uniqueness statement follows by expanding
  `‖U t - Z t‖ ^ 2` into three such constant pairings and using positivity of the actual `L2`
  norm.  No ODE existence or uniqueness theorem in Banach space is used, and no smoothness of
  `gamma` is assumed — only that its values are unit vectors.
* `radial_characterization` (G3): along `radialCurve e` a field is parallel exactly when it is
  `t ↦ liftedFrame t e W` for a unique fixed `W`.  Existence of `W` uses surjectivity of the
  frame at the parameter `0` (7B.1) and then G2 to propagate the equality; uniqueness uses
  that the frame is a linear isometry.  The reverse implication proves all three parallelity
  conditions, tangency and differentiability included.
* `radial_transport` (G4): for arbitrary real parameters `s, t` there is a unique linear
  isometry equivalence between the explicit hyperplanes at `radialCurve e s` and
  `radialCurve e t` such that each `x` is connected to its image by an actual parallel field.
  The candidate is the composition of the two onto frame equivalences of 7B.1, and its
  characterization and uniqueness both come from G2/G3; equal parameters, `0`, `π / 2`, `π`,
  negative parameters and the zero vector are all covered, and no trigonometric denominator
  occurs.

Scope caveat.  This is unique parallel transport for the explicit extrinsic projected
derivative along the explicit parametrized radial curve.  At the antipode it is transport
along that curve; nothing is claimed about uniqueness of a geodesic joining the endpoints or
about path-independence of transport.  No bundled Mathlib manifold connection or intrinsic Lie
bracket is identified, no general manifold-field extension or connection uniqueness theorem is
proved, and intrinsic path-length distance, its squared-distance Hessian and the normalized
metric recovery remain open; the inherited chord distance is not used as a geodesic distance.
-/

namespace SphericalProofRequest7B3

open SphericalProofRequest7B1 SphericalProofRequest7B2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

def IsParallelAlong (gamma U : Real → Ambient V) : Prop :=
  (∀ t : Real, U t ∈ tangentPlane (gamma t)) ∧
  (∀ t : Real, DifferentiableAt Real U t) ∧
  (∀ t : Real, covariantAlong gamma U t = 0)

-- G1: actual inner-product differentiation expressed by the projected derivative.
def GoalAlongMetric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (gamma U Z : Real → Ambient V) (t : Real),
    ‖gamma t‖=1 → U t ∈ tangentPlane (gamma t) → Z t ∈ tangentPlane (gamma t) →
    DifferentiableAt Real U t → DifferentiableAt Real Z t →
    HasDerivAt (fun s => inner Real (U s) (Z s))
      (inner Real (covariantAlong gamma U t) (Z t) +
        inner Real (U t) (covariantAlong gamma Z t)) t

-- G2: preservation and uniqueness follow for every parallel pair on all of R.
def GoalParallelUniqueness (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (gamma U Z : Real → Ambient V), (∀ t : Real, ‖gamma t‖=1) →
    IsParallelAlong gamma U → IsParallelAlong gamma Z →
    (∀ s t : Real, inner Real (U t) (Z t) = inner Real (U s) (Z s)) ∧
    (∀ s : Real, U s=Z s → ∀ t : Real, U t=Z t)

-- G3: all parallel fields along the actual radial curve have one fixed frame coordinate.
def GoalRadialCharacterization (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (e : V), ‖e‖=1 → ∀ U : Real → Ambient V,
    IsParallelAlong (radialCurve e) U ↔ ∃! W : V, ∀ t : Real, U t=liftedFrame t e W

-- G4: transport is characterized by parallel curves, not merely by an arbitrary isometry.
def GoalRadialTransport (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (e : V), ‖e‖=1 → ∀ s t : Real,
    ∃! T : ↥(tangentPlane (radialCurve e s)) ≃ₗᵢ[Real] ↥(tangentPlane (radialCurve e t)),
      ∀ x : ↥(tangentPlane (radialCurve e s)),
        ∃ U : Real → Ambient V, IsParallelAlong (radialCurve e) U ∧
          U s=(x : Ambient V) ∧ U t=(T x : Ambient V)


/-! ### Supporting lemmas: differentiating the pairing of two fields -/

/-- The actual derivative of the pointwise inner product of two fields, expressed through the
projected derivatives; this is the content of G1 and needs no hypothesis on `gamma`. -/
lemma hasDerivAt_inner_of_tangent (gamma U Z : Real → Ambient V) (t : Real)
    (hU : U t ∈ tangentPlane (gamma t)) (hZ : Z t ∈ tangentPlane (gamma t))
    (hUd : DifferentiableAt Real U t) (hZd : DifferentiableAt Real Z t) :
    HasDerivAt (fun s => (inner Real (U s) (Z s) : Real))
      ((inner Real (covariantAlong gamma U t) (Z t) : Real) +
        inner Real (U t) (covariantAlong gamma Z t)) t := by
  have hd : HasDerivAt (fun s => (inner Real (U s) (Z s) : Real))
      ((inner Real (U t) (deriv Z t) : Real) + inner Real (deriv U t) (Z t)) t :=
    hUd.hasDerivAt.inner Real hZd.hasDerivAt
  refine hd.congr_deriv ?_
  rw [covariantAlong, covariantAlong, inner_tangentProjection_left (gamma t) (deriv U t) hZ,
    inner_tangentProjection_right (gamma t) (deriv Z t) hU]
  exact add_comm _ _

/-- For two parallel fields the pointwise pairing is a constant function of the parameter. -/
lemma inner_const_of_parallel {gamma U Z : Real → Ambient V}
    (hU : IsParallelAlong gamma U) (hZ : IsParallelAlong gamma Z) (s t : Real) :
    (inner Real (U t) (Z t) : Real) = inner Real (U s) (Z s) := by
  obtain ⟨hUt, hUd, hUc⟩ := hU
  obtain ⟨hZt, hZd, hZc⟩ := hZ
  have hderiv : ∀ r : Real,
      HasDerivAt (fun u => (inner Real (U u) (Z u) : Real)) 0 r := by
    intro r
    have h := hasDerivAt_inner_of_tangent gamma U Z r (hUt r) (hZt r) (hUd r) (hZd r)
    rw [hUc r, hZc r] at h
    simpa using h
  have hdiff : Differentiable Real (fun u => (inner Real (U u) (Z u) : Real)) :=
    fun r => (hderiv r).differentiableAt
  have hzero : ∀ r : Real, deriv (fun u => (inner Real (U u) (Z u) : Real)) r = 0 :=
    fun r => (hderiv r).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t s

/-! ### Supporting lemmas: the moving frame as a family of parallel fields -/

/-- The 7B.1 moving frame is a parallel field along the radial curve, in the full sense of
`IsParallelAlong`: it is tangent, differentiable and has vanishing projected derivative. -/
lemma isParallelAlong_liftedFrame (e : V) (he : ‖e‖ = 1) (W : V) :
    IsParallelAlong (radialCurve e) (fun u : Real => liftedFrame u e W) := by
  refine ⟨fun t => liftedFrame_mem_tangentPlane e he t W,
    fun t => (hasDerivAt_liftedFrame e t W).differentiableAt, fun t => ?_⟩
  rw [covariantAlong, (hasDerivAt_liftedFrame e t W).deriv]
  exact tangentProjection_smul_self (norm_radialCurve e he t) _

/-- The moving frame is injective at every parameter, being a linear isometry. -/
lemma liftedFrame_injective (e : V) (he : ‖e‖ = 1) (t : Real) {W W' : V}
    (h : liftedFrame t e W = liftedFrame t e W') : W = W' := by
  have h0 : liftedFrame t e (W - W') = 0 := by rw [map_sub, h, sub_self]
  have : ‖W - W'‖ = 0 := by rw [← norm_liftedFrame e he t, h0, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- The 7B.1 moving frame packaged as a linear isometry *equivalence* onto the tangent
hyperplane; this is the onto frame of 7B.1 G3, made available as a definition. -/
noncomputable def frameEquiv (e : V) (he : ‖e‖ = 1) (t : Real) :
    V ≃ₗᵢ[Real] ↥(tangentPlane (radialCurve e t)) :=
  LinearIsometryEquiv.ofSurjective (frameLinearIsometry e he t) (by
    rintro ⟨z, hz⟩
    obtain ⟨W, hW⟩ := liftedFrame_surjective e he t hz
    exact ⟨W, Subtype.ext hW⟩)

@[simp] lemma frameEquiv_coe (e : V) (he : ‖e‖ = 1) (t : Real) (W : V) :
    ((frameEquiv e he t W : ↥(tangentPlane (radialCurve e t))) : Ambient V)
      = liftedFrame t e W := rfl

lemma frameEquiv_symm_coe (e : V) (he : ‖e‖ = 1) (t : Real)
    (x : ↥(tangentPlane (radialCurve e t))) :
    liftedFrame t e ((frameEquiv e he t).symm x) = (x : Ambient V) := by
  rw [← frameEquiv_coe e he t, LinearIsometryEquiv.apply_symm_apply]


/-! ### Requested theorems -/

/-- G1.  If the values `U t` and `Z t` are tangent at `gamma t` and both fields are
differentiable at `t`, the genuine derivative of `s ↦ ⟪U s, Z s⟫` at `t` is
`⟪D_t U, Z t⟫ + ⟪U t, D_t Z⟫`.  The actual inner product is differentiated first; the ambient
derivatives may then be replaced by their tangential projections, because the discarded radial
component pairs trivially with the tangent vectors `Z t` and `U t`.  Transparency note: the
hypothesis `‖gamma t‖ = 1` is framing and is not used; it is retained as specified. -/
theorem along_metric : GoalAlongMetric V := by
  intro gamma U Z t _hgamma hU hZ hUd hZd
  exact hasDerivAt_inner_of_tangent gamma U Z t hU hZ hUd hZd

/-- G2.  Along a unit-valued curve, any two parallel fields have constant pairing, and two
parallel fields agreeing at a single parameter agree everywhere.  Constancy is G1 (whose
derivative term vanishes by parallelity) together with the real theorem that a differentiable
function with everywhere vanishing derivative is constant.  Uniqueness expands
`‖U t - Z t‖ ^ 2 = ⟪U t, U t⟫ - 2 ⟪U t, Z t⟫ + ⟪Z t, Z t⟫`, which is constant since each of
the three pairings is, and vanishes at the given parameter; positivity of the actual `L2`
norm then forces `U t = Z t`.  No ODE existence or uniqueness theorem, and no smoothness of
`gamma`, is used.  Transparency note: the hypothesis `‖gamma t‖ = 1` is not needed. -/
theorem parallel_uniqueness : GoalParallelUniqueness V := by
  intro gamma U Z _hgamma hU hZ
  refine ⟨fun s t => inner_const_of_parallel hU hZ s t, ?_⟩
  intro s hs t
  have hUU := inner_const_of_parallel hU hU s t
  have hZZ := inner_const_of_parallel hZ hZ s t
  have hUZ := inner_const_of_parallel hU hZ s t
  have hZU := inner_const_of_parallel hZ hU s t
  have hnorm : ‖U t - Z t‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [hUU, hZZ, hUZ, hZU, hs]
    ring
  have : U t - Z t = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnorm
    exact norm_eq_zero.mp this
  exact sub_eq_zero.mp this

/-- G3.  A field along `radialCurve e` is parallel exactly when it is the frame field
`t ↦ liftedFrame t e W` of a unique fixed `W`.  For the forward direction the value `U 0` is
tangent, hence is `liftedFrame 0 e W` for some `W` by the 7B.1 surjectivity of the frame; the
frame field is itself parallel, so G2 propagates the equality to every parameter.  The `W` is
unique because the frame is a linear isometry, hence injective.  The reverse direction
establishes all three parallelity conditions, tangency and differentiability included, not
merely the vanishing of the projected derivative. -/
theorem radial_characterization : GoalRadialCharacterization V := by
  intro e he U
  constructor
  · intro hU
    obtain ⟨W, hW⟩ := liftedFrame_surjective e he 0 (hU.1 0)
    refine ⟨W, ?_, ?_⟩
    · intro t
      exact (parallel_uniqueness (V := V) (radialCurve e) U _
        (fun r => norm_radialCurve e he r) hU (isParallelAlong_liftedFrame e he W)).2
        0 hW.symm t
    · intro W' hW'
      refine liftedFrame_injective e he 0 ?_
      rw [hW, ← hW' 0]
  · rintro ⟨W, hW, -⟩
    have hfun : U = fun u : Real => liftedFrame u e W := funext hW
    rw [hfun]
    exact isParallelAlong_liftedFrame e he W

/-- G4.  For arbitrary real parameters `s` and `t` (equal parameters, `0`, `π / 2`, `π` and
negative values included) there is exactly one linear isometry equivalence between the
explicit hyperplanes at `radialCurve e s` and `radialCurve e t` with the property that every
`x` is joined to its image by an actual parallel field along the curve.  The candidate is the
composition of the two onto frame equivalences of 7B.1; the connecting field is the frame
field of the frame coordinate of `x`, which is parallel, and it takes the value `x` at `s`
(the zero vector included).  Uniqueness holds because, by G3, any parallel field through `x`
at `s` is a frame field with a determined coordinate, so its value at `t` is forced. -/
theorem radial_transport : GoalRadialTransport V := by
  intro e he s t
  refine ⟨(frameEquiv e he s).symm.trans (frameEquiv e he t), ?_, ?_⟩
  · intro x
    refine ⟨fun u : Real => liftedFrame u e ((frameEquiv e he s).symm x),
      isParallelAlong_liftedFrame e he _, frameEquiv_symm_coe e he s x, rfl⟩
  · intro T hT
    refine LinearIsometryEquiv.ext fun x => Subtype.ext ?_
    obtain ⟨U, hUpar, hUs, hUt⟩ := hT x
    obtain ⟨W, hW, -⟩ := (radial_characterization (V := V) e he U).mp hUpar
    have hWs : (frameEquiv e he s).symm x = W := by
      refine liftedFrame_injective e he s ?_
      rw [frameEquiv_symm_coe e he s x, ← hUs, hW s]
    rw [← hUt, hW t]
    show liftedFrame t e W = _
    rw [← hWs]
    rfl

end SphericalProofRequest7B3
