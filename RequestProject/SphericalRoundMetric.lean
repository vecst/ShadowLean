import RequestProject.SphericalBundledTangent
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The smooth round Riemannian metric on the unit sphere (milestone 7B.6, Run 2)

This module builds the round Riemannian metric on Mathlib's manifold tangent bundle of the
unit sphere `UnitSphere V ⊆ Ambient V`, as a bundled
`Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) ·)`.

The metric is the ambient inner product pulled back through the differential
`tangentInclusion n p` of the inclusion `sphereInclusion` (Run 1). All the structure fields are
proved: fiberwise bilinearity and continuity, symmetry, strict positivity, the bounded-unit-ball
condition, and smoothness of the resulting section of the bundle of bilinear forms, expressed in
bundle coordinates.
-/

namespace SphericalProofRequest7B6

open SphericalProofRequest7B1 SphericalProofRequest7B4
open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

-- G3: a genuine smooth Riemannian metric on the existing manifold tangent bundle.
-- The prescribed pairing is proved positive and smooth, not assumed to be a metric.
def GoalRoundMetric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (n : Nat)
    [Fact (Module.finrank Real (Ambient V) = n + 1)] : Prop :=
  ∃ g : Bundle.ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace Real (Fin n))
      (fun p : UnitSphere V => TangentSpace (𝓡 n) p),
    ∀ (p : UnitSphere V) (u v : TangentSpace (𝓡 n) p),
      g.inner p u v = roundPairing n p u v

section Pullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace Real W]

/-- Pull back the inner product of `W` along a continuous linear map `T : F →L[ℝ] W`,
as a continuous bilinear form on `F`. -/
noncomputable def pullbackForm (T : F →L[Real] W) : F →L[Real] F →L[Real] Real :=
  (ContinuousLinearMap.compL Real F W Real).flip T ∘L
    (ContinuousLinearMap.compL Real F W (W →L[Real] Real) (innerSL Real) T)

@[simp] lemma pullbackForm_apply (T : F →L[Real] W) (u v : F) :
    pullbackForm T u v = inner Real (T u) (T v) := rfl

/-- The pullback of the inner product depends smoothly (indeed, quadratically) on the map. -/
lemma contDiff_pullbackForm {m : WithTop ℕ∞} :
    ContDiff Real m (fun T : F →L[Real] W => pullbackForm T) :=
  (ContinuousLinearMap.contDiff _).clm_comp (ContinuousLinearMap.contDiff _)

end Pullback

section Metric

variable (n : Nat) [Fact (Module.finrank Real (Ambient V) = n + 1)]

/-- The round fiberwise bilinear form: the ambient inner product pulled back through the
differential of the inclusion of the sphere. -/
noncomputable def roundInner (p : UnitSphere V) :
    TangentSpace (𝓡 n) p →L[Real] TangentSpace (𝓡 n) p →L[Real] Real :=
  pullbackForm (F := EuclideanSpace Real (Fin n)) (tangentInclusion n p)

omit [FiniteDimensional Real V] in
lemma roundInner_apply (p : UnitSphere V) (u v : TangentSpace (𝓡 n) p) :
    roundInner n p u v = roundPairing n p u v := rfl

omit [FiniteDimensional Real V] in
lemma roundInner_symm (p : UnitSphere V) (u v : TangentSpace (𝓡 n) p) :
    roundInner n p u v = roundInner n p v u := by
  simp only [roundInner_apply, roundPairing, real_inner_comm]

lemma roundInner_pos (p : UnitSphere V) (u : TangentSpace (𝓡 n) p) (hu : u ≠ 0) :
    0 < roundInner n p u u := by
  have hinj : Function.Injective (tangentInclusion n p) := (tangent_inclusion (V := V) n p).2.1
  have hne : tangentInclusion n p u ≠ 0 := fun h => hu (hinj (by simpa using h))
  rw [roundInner_apply]
  exact real_inner_self_pos.mpr hne

lemma roundInner_isVonNBounded (p : UnitSphere V) :
    Bornology.IsVonNBounded Real {u : TangentSpace (𝓡 n) p | roundInner n p u u < 1} := by
  have hinj : Function.Injective (tangentInclusion n p) := (tangent_inclusion (V := V) n p).2.1
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith
      (E := EuclideanSpace Real (Fin n)) (F := Ambient V)
      ((tangentInclusion n p).toLinearMap) (LinearMap.ker_eq_bot.2 hinj)
  show Bornology.IsVonNBounded Real
    {u : EuclideanSpace Real (Fin n) | roundInner n p u u < 1}
  rw [NormedSpace.isVonNBounded_iff]
  apply Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : EuclideanSpace Real (Fin n))) (r := K))
  intro u hu
  have hu' : inner Real (tangentInclusion n p u) (tangentInclusion n p u) < 1 := hu
  rw [real_inner_self_eq_norm_sq] at hu'
  have h2 : ‖u‖ ≤ K * ‖tangentInclusion n p u‖ :=
    ZeroHomClass.bound_of_antilipschitz _ hanti u
  have hball : ‖u‖ ≤ (K : Real) := by
    nlinarith [norm_nonneg (tangentInclusion n p u), hK.le]
  simpa [dist_zero_right] using hball

omit [FiniteDimensional Real V] in
/-- The differential of the inclusion, read in the bundle coordinates of the tangent bundle,
is the composition of the differential with the inverse trivialization. -/
lemma inTangentCoordinates_sphereInclusion (p₀ x : UnitSphere V) :
    inTangentCoordinates (𝓡 n) 𝓘(Real, Ambient V) id sphereInclusion
      (fun y => tangentInclusion n y) p₀ x
      = tangentInclusion n x ∘L
        (trivializationAt (EuclideanSpace Real (Fin n)) (TangentSpace (𝓡 n)) p₀).symmL Real x := by
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space, id_eq]
  exact ContinuousLinearMap.ext fun v => rfl

omit [FiniteDimensional Real V] in
/-- Near a base point, the round bilinear form read in bundle coordinates is the pullback of the
ambient inner product along the differential of the inclusion read in tangent coordinates. -/
lemma roundInner_inCoordinates (p₀ x : UnitSphere V)
    (hx : x ∈ (trivializationAt (EuclideanSpace Real (Fin n)) (TangentSpace (𝓡 n)) p₀).baseSet) :
    ContinuousLinearMap.inCoordinates (EuclideanSpace Real (Fin n)) (TangentSpace (𝓡 n))
      (EuclideanSpace Real (Fin n) →L[Real] Real) (fun b => TangentSpace (𝓡 n) b →L[Real] Real)
      p₀ x p₀ x (roundInner n x)
      = pullbackForm (inTangentCoordinates (𝓡 n) 𝓘(Real, Ambient V) id sphereInclusion
          (fun y => tangentInclusion n y) p₀ x) := by
  rw [inTangentCoordinates_sphereInclusion]
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial (UnitSphere V) Real) (F₃ := Real) hx hx
    (by simp)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, pullbackForm_apply, ContinuousLinearMap.comp_apply,
    Bundle.Trivialization.symmL_apply _ hx, roundInner_apply, roundPairing]

omit [FiniteDimensional Real V] in
/-- The round bilinear form is a smooth section of the bundle of bilinear forms on the tangent
bundle, i.e. it is smooth when read in bundle coordinates. -/
lemma roundInner_contMDiff :
    ContMDiff (𝓡 n) ((𝓡 n).prod
        𝓘(Real, EuclideanSpace Real (Fin n) →L[Real] EuclideanSpace Real (Fin n) →L[Real] Real)) ∞
      (fun p : UnitSphere V => Bundle.TotalSpace.mk'
        (EuclideanSpace Real (Fin n) →L[Real] EuclideanSpace Real (Fin n) →L[Real] Real)
        p (roundInner n p)) := by
  intro p₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hf : ContMDiffAt (𝓡 n) 𝓘(Real, Ambient V) ω sphereInclusion p₀ :=
    (contMDiff_coe_sphere (E := Ambient V) (n := n) (m := ω)).contMDiffAt
  have hT : ContMDiffAt (𝓡 n) 𝓘(Real, EuclideanSpace Real (Fin n) →L[Real] Ambient V) ∞
      (inTangentCoordinates (𝓡 n) 𝓘(Real, Ambient V) id sphereInclusion
        (fun y => tangentInclusion n y) p₀) p₀ := hf.mfderiv_const (m := ∞) (by simp)
  have hP : ContMDiffAt (𝓡 n)
      𝓘(Real, EuclideanSpace Real (Fin n) →L[Real] EuclideanSpace Real (Fin n) →L[Real] Real) ∞
      (fun x => pullbackForm (inTangentCoordinates (𝓡 n) 𝓘(Real, Ambient V) id sphereInclusion
        (fun y => tangentInclusion n y) p₀ x)) p₀ :=
    ContDiff.comp_contMDiffAt contDiff_pullbackForm hT
  refine hP.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt (EuclideanSpace Real (Fin n))
      (TangentSpace (𝓡 n)) p₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (F := EuclideanSpace Real (Fin n))
        (E := TangentSpace (𝓡 n) (M := UnitSphere V)) p₀)] with x hx
  exact roundInner_inCoordinates n p₀ x hx

/-- G3: the round metric is a genuine smooth Riemannian metric on the tangent bundle of the
unit sphere, whose fiberwise inner product is the prescribed pairing. -/
theorem round_metric (n : Nat) [Fact (Module.finrank Real (Ambient V) = n + 1)] :
    GoalRoundMetric V n :=
  ⟨{ inner := roundInner n
     symm := roundInner_symm n
     pos := roundInner_pos n
     isVonNBounded := roundInner_isVonNBounded n
     contMDiff := roundInner_contMDiff n }, fun _ _ _ => rfl⟩

end Metric

end SphericalProofRequest7B6
