import RequestProject.SphericalPathDistance
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Bundled tangent bridge for the unit sphere (milestone 7B.6, Run 1)

This module connects the ambient hyperplane picture used in the earlier spherical
modules with Mathlib's actual manifold tangent bundle of the unit sphere.

`UnitSphere V` is the standard subtype `Metric.sphere (0 : Ambient V) 1` in the L2 ambient
space `Ambient V = WithLp 2 (ℝ × V)`, carrying its existing Mathlib stereographic charted
structure with model `𝓡 n` (which requires `Fact (finrank ℝ (Ambient V) = n + 1)`).
`tangentInclusion n p` is the honest `mfderiv` of the inclusion `sphereInclusion` at `p`,
and `roundPairing` pulls the ambient inner product back through it.

Results proved here:

* `tangent_inclusion` (G1): at every sphere point the inclusion is `MDifferentiableAt`, its
  differential is injective, and the range of that differential equals the previously used
  ambient hyperplane `tangentPlane (p : Ambient V) = ker (innerSL ℝ p)`.
* `tangent_equivalence` (G2): the differential, corestricted to that hyperplane, is the
  unique continuous linear equivalence `TangentSpace (𝓡 n) p ≃L[ℝ] ↥(tangentPlane p)` whose
  ambient action is exactly `tangentInclusion n p`; uniqueness is derived from the action
  equation alone.

Scope. No new sphere atlas, Riemannian metric instance or gradient operator is introduced
here; the smooth round metric (Run 2) and the bundled gradient (Run 3) remain open. No
`Nontrivial V` or positive-dimension hypothesis is used: the statements cover all points of
the sphere, zero tangent vectors and `n = 0`.
-/

namespace SphericalProofRequest7B6

open SphericalProofRequest7B1 SphericalProofRequest7B4
open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

abbrev UnitSphere (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] :=
  ↥(Metric.sphere (0 : Ambient V) 1)

def sphereInclusion (p : UnitSphere V) : Ambient V := p

variable [FiniteDimensional Real V]

noncomputable def tangentInclusion (n : Nat)
    [Fact (Module.finrank Real (Ambient V) = n + 1)] (p : UnitSphere V) :
    TangentSpace (𝓡 n) p →L[Real] Ambient V :=
  mfderiv (𝓡 n) 𝓘(Real, Ambient V) sphereInclusion p

-- Pull back the actual ambient inner product through the actual inclusion differential.
noncomputable def roundPairing (n : Nat)
    [Fact (Module.finrank Real (Ambient V) = n + 1)] (p : UnitSphere V)
    (u v : TangentSpace (𝓡 n) p) : Real :=
  inner Real (tangentInclusion n p u) (tangentInclusion n p v)

-- G1: connect the actual manifold differential with the old tangent hyperplane.
def GoalTangentInclusion (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (n : Nat)
    [Fact (Module.finrank Real (Ambient V) = n + 1)] : Prop :=
  ∀ p : UnitSphere V,
    MDifferentiableAt (𝓡 n) 𝓘(Real, Ambient V) sphereInclusion p ∧
    Function.Injective (tangentInclusion n p) ∧
    (tangentInclusion n p).range = tangentPlane (p : Ambient V)

-- G2: the equivalence must be the inclusion differential, not an arbitrary isomorphism.
def GoalTangentEquivalence (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (n : Nat)
    [Fact (Module.finrank Real (Ambient V) = n + 1)] : Prop :=
  ∀ p : UnitSphere V,
    ∃! T : TangentSpace (𝓡 n) p ≃L[Real] ↥(tangentPlane (p : Ambient V)),
      ∀ u : TangentSpace (𝓡 n) p, (T u : Ambient V) = tangentInclusion n p u


omit [FiniteDimensional Real V] in
/-- The old hyperplane `tangentPlane p = ker (innerSL ℝ p)` is exactly the orthogonal
complement of the line spanned by `p`, which is the form in which Mathlib describes the
range of the sphere inclusion differential. -/
lemma tangentPlane_eq_orthogonal (p : Ambient V) :
    tangentPlane p = (Submodule.span Real {p})ᗮ := by
  ext x
  simp [tangentPlane, Submodule.mem_orthogonal_singleton_iff_inner_right]

/-- G1: the inclusion of the sphere is manifold-differentiable at every point, its
differential is injective, and its range is the old ambient hyperplane. -/
theorem tangent_inclusion (n : Nat) [Fact (Module.finrank Real (Ambient V) = n + 1)] :
    GoalTangentInclusion V n := by
  intro p
  refine ⟨(contMDiff_coe_sphere (E := Ambient V) (n := n) (m := 1) p).mdifferentiableAt
      one_ne_zero, mfderiv_coe_sphere_injective p, ?_⟩
  have h := range_mfderiv_coe_sphere (E := Ambient V) (n := n) p
  rw [tangentPlane_eq_orthogonal]
  exact h

/-- G2: the inclusion differential, with codomain restricted to the old hyperplane, is the
unique continuous linear equivalence whose ambient action is `tangentInclusion`. -/
theorem tangent_equivalence (n : Nat) [Fact (Module.finrank Real (Ambient V) = n + 1)] :
    GoalTangentEquivalence V n := by
  intro p
  obtain ⟨-, hinj, hrange⟩ := tangent_inclusion (V := V) n p
  have hmem : ∀ u : TangentSpace (𝓡 n) p, tangentInclusion n p u ∈ tangentPlane (p : Ambient V) :=
    fun u => hrange ▸ ⟨u, rfl⟩
  set L : TangentSpace (𝓡 n) p →L[Real] ↥(tangentPlane (p : Ambient V)) :=
    (tangentInclusion n p).codRestrict _ hmem with hL
  have hLinj : Function.Injective L := by
    intro u v huv
    exact hinj (congrArg Subtype.val huv)
  have hLsurj : Function.Surjective L := by
    rintro ⟨x, hx⟩
    rw [← hrange] at hx
    obtain ⟨u, hu⟩ := hx
    exact ⟨u, Subtype.ext hu⟩
  have : FiniteDimensional Real (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (FiniteDimensional Real (EuclideanSpace Real (Fin n)))
  have : T2Space (TangentSpace (𝓡 n) p) :=
    inferInstanceAs (T2Space (EuclideanSpace Real (Fin n)))
  let T : TangentSpace (𝓡 n) p ≃L[Real] ↥(tangentPlane (p : Ambient V)) :=
    (LinearEquiv.ofBijective (L : TangentSpace (𝓡 n) p →ₗ[Real] _)
      ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv
  have hTaction : ∀ u : TangentSpace (𝓡 n) p, (T u : Ambient V) = tangentInclusion n p u := by
    intro u
    simp [T, hL]
  refine ⟨T, hTaction, ?_⟩
  intro T' hT'
  refine ContinuousLinearEquiv.ext (funext fun u => Subtype.ext ?_)
  rw [hT' u, hTaction u]

end SphericalProofRequest7B6
