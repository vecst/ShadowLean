import RequestProject.SphericalRoundMetric
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The bundled gradient of the angular potential (milestone 7B.6, Run 3)

This module proves G4: at a point `p` of the unit sphere whose ambient height satisfies
`-1 < height p < 1`, the restriction of the previously studied ambient angular potential
`angularPotential` (7B.4) to the manifold `UnitSphere V` is `MDifferentiableAt` for the model
`𝓡 n`, and it has a unique tangent-vector gradient `G` for the round pairing `roundPairing`
of Run 1 (which Run 2 proved is the fiberwise inner product of a genuine smooth Riemannian
metric).

The gradient is obtained from the actual inclusion differential: `angularGradient p` was
proved tangent in 7B.4, and Run 1's `tangent_inclusion` identifies the range of
`tangentInclusion n p` with the ambient hyperplane `tangentPlane p`, so there is a unique
tangent vector `G` with `tangentInclusion n p G = angularGradient p`. Chaining the ambient
Frechet derivative of `angularPotential` (7B.4's `potential_gradient`) with the inclusion
differential shows that the actual `mfderiv` of the restricted potential is represented by
`G` through `roundPairing`. Uniqueness follows from injectivity of `tangentInclusion n p`.

Scope. The statement is pointwise and excludes both poles, as the ambient gradient extension
is only differentiated on `-1 < height p < 1`. No vector-field smoothness, Hessian,
connection or distance-comparison statement is claimed here.
-/

namespace SphericalProofRequest7B6

open SphericalProofRequest7B1 SphericalProofRequest7B4
open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

-- G4: genuine manifold differentiability and the unique gradient for that pairing.
-- It is identified with the previously differentiated angularGradient under G2.
def GoalBundledGradient (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V] (n : Nat)
    [Fact (Module.finrank Real (Ambient V) = n + 1)] : Prop :=
  ∀ p : UnitSphere V, -1 < height (p : Ambient V) → height (p : Ambient V) < 1 →
    MDifferentiableAt (𝓡 n) 𝓘(Real) (fun q : UnitSphere V => angularPotential (q : Ambient V)) p ∧
    (∃! G : TangentSpace (𝓡 n) p,
      tangentInclusion n p G = angularGradient (p : Ambient V) ∧
      ∀ u : TangentSpace (𝓡 n) p,
        mfderiv (𝓡 n) 𝓘(Real) (fun q : UnitSphere V => angularPotential (q : Ambient V)) p u =
          roundPairing n p G u)


/-- G4: the restricted angular potential is manifold-differentiable at every non-polar sphere
point, and it has a unique tangent gradient for the round pairing; that gradient is exactly the
preimage of the ambient `angularGradient` under the inclusion differential. -/
theorem bundled_gradient (n : Nat) [Fact (Module.finrank Real (Ambient V) = n + 1)] :
    GoalBundledGradient V n := by
  intro p h1 h2
  have hp : ‖(p : Ambient V)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  obtain ⟨hincl, hinj, hrange⟩ := tangent_inclusion (V := V) n p
  obtain ⟨hpot, -, hgradmem, hrep⟩ := potential_gradient (V := V) (p : Ambient V) hp h1 h2
  have hamb : MDifferentiableAt 𝓘(Real, Ambient V) 𝓘(Real) angularPotential (p : Ambient V) :=
    mdifferentiableAt_iff_differentiableAt.2 hpot.differentiableAt
  have hcomp : MDifferentiableAt (𝓡 n) 𝓘(Real)
      (fun q : UnitSphere V => angularPotential (q : Ambient V)) p := hamb.comp p hincl
  refine ⟨hcomp, ?_⟩
  have hmfderiv : ∀ u : TangentSpace (𝓡 n) p,
      mfderiv (𝓡 n) 𝓘(Real) (fun q : UnitSphere V => angularPotential (q : Ambient V)) p u
        = fderiv Real angularPotential (p : Ambient V) (tangentInclusion n p u) := by
    intro u
    have hchain := mfderiv_comp (I := 𝓡 n) (I' := 𝓘(Real, Ambient V)) (I'' := 𝓘(Real))
      (f := sphereInclusion) (g := angularPotential) p hamb hincl
    rw [show (fun q : UnitSphere V => angularPotential (q : Ambient V))
        = angularPotential ∘ sphereInclusion from rfl, hchain]
    simp only [tangentInclusion, mfderiv_eq_fderiv]
    rfl
  have hmem : angularGradient (p : Ambient V) ∈ (tangentInclusion n p).range := by
    rw [hrange]; exact hgradmem
  obtain ⟨G, hG⟩ := hmem
  refine ⟨G, ⟨hG, fun u => ?_⟩, ?_⟩
  · rw [hmfderiv u, hrep _ (hrange ▸ ⟨u, rfl⟩), roundPairing, ← hG]
    rfl
  · rintro G' ⟨hG', -⟩
    exact hinj (hG'.trans hG.symm)

end SphericalProofRequest7B6
