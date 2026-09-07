import RequestProject.SphericalFullLogarithm

/-!
# Spherical repair 7A.3: exponential differential and coordinate factorization

This module proves the five Goal propositions stated below (their statements are
unchanged from the reviewed specification):

* `exp_derivative` (G1): the sinc exponential `expCoordinates` of 7A.1 has the Frechet
  derivative `expDerivative r e` at `r • e`, for `0 < r < π` and `‖e‖ = 1`.  It is
  obtained by differentiating the actual sinc formula, using its local agreement with
  `X ↦ (cos ‖X‖, (sin ‖X‖ / ‖X‖) • X)` away from the origin.
* `jacobi_inverse` (G2): `jacobiMap r e` and `inverseJacobiMap r e` are two-sided
  inverses as continuous linear maps on the branch `0 < r < π`, `‖e‖ = 1`.
* `coordinate_identities` (G3): coordinate factorizations of the previously proved
  derivatives through `coordinateLift`.
* `composition_factorization` (G4): the actual composition `Y ↦ fullLog (productMap r e Y)`
  has Frechet derivative `(0, inverseJacobiMap ∘ compressionMap)` at `0`; it is obtained
  from 7A.2's `composition_derivative`.
* `radial_and_equator` (G5): the radial directions are fixed by `jacobiMap`,
  `inverseJacobiMap`, `compressionMap`, together with an explicit Euclidean two
  dimensional witness at `r = π / 2` where the transverse actions are `2 / π`, `π / 2`
  and `0`, matching the actual Frechet derivatives of G1 and G4.

Scope caveat. `coordinateLift` is an explicit coordinate map; nothing here identifies it
as geometric parallel transport, nor as an isometry of the product maximum norm.  These
are coordinate Frechet derivative statements: they do not establish a sphere connection,
an intrinsic path length distance, or a covariant Hessian.
-/
namespace SphericalProofRequest7A3

open SphericalProofRequest7A1 SphericalProofRequest7A2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

noncomputable def expDerivative (r : Real) (e : V) : V →L[Real] (Real × V) :=
  ((-Real.sin r) • innerSL Real e).prod
    ((Real.cos r) • radialProjection e + (Real.sin r / r) • transverseProjection e)

noncomputable def coordinateLift (r : Real) (e : V) : V →L[Real] (Real × V) :=
  ((-Real.sin r) • innerSL Real e).prod
    ((Real.cos r) • radialProjection e + transverseProjection e)

noncomputable def jacobiMap (r : Real) (e : V) : V →L[Real] V :=
  radialProjection e + (Real.sin r / r) • transverseProjection e

noncomputable def inverseJacobiMap (r : Real) (e : V) : V →L[Real] V :=
  radialProjection e + (r / Real.sin r) • transverseProjection e

noncomputable def compressionMap (r : Real) (e : V) : V →L[Real] V :=
  radialProjection e + (Real.cos r) • transverseProjection e

-- G1: independently differentiate the existing sinc exponential away from zero.
def GoalExpDerivative (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    HasFDerivAt (expCoordinates : V → Real × V) (expDerivative r e) (r • e)

-- G2: actual two-sided linear inverse on the specified branch.
def GoalJacobiInverse (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    (inverseJacobiMap r e).comp (jacobiMap r e) = ContinuousLinearMap.id Real V ∧
    (jacobiMap r e).comp (inverseJacobiMap r e) = ContinuousLinearMap.id Real V

-- G3: compare independently proved derivatives using the explicit coordinate lift.
def GoalCoordinateIdentities (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    expDerivative r e = (coordinateLift r e).comp (jacobiMap r e) ∧
    productDerivative r e = (coordinateLift r e).comp (compressionMap r e) ∧
    (logDerivative r e).comp (coordinateLift r e) =
      (0 : V →L[Real] Real).prod (inverseJacobiMap r e)

-- G4: the actual full-log composition has the inverse-Jacobi-times-compression derivative.
def GoalCompositionFactorization (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    HasFDerivAt (fun Y : V => fullLog (productMap r e Y))
      ((0 : V →L[Real] Real).prod ((inverseJacobiMap r e).comp (compressionMap r e))) 0

-- G5: radial directions survive and actual transverse derivatives distinguish the operators.
def GoalRadialAndEquator : Prop :=
  (∀ (r : Real) (e : EuclideanSpace Real (Fin 2)),
    0 < r → r < Real.pi → ‖e‖ = 1 →
      jacobiMap r e e = e ∧ inverseJacobiMap r e e = e ∧ compressionMap r e e = e) ∧
  (∃ e W : EuclideanSpace Real (Fin 2),
    ‖e‖ = 1 ∧ ‖W‖ = 1 ∧ inner Real e W = 0 ∧
    jacobiMap (Real.pi / 2) e W = (2 / Real.pi) • W ∧
    inverseJacobiMap (Real.pi / 2) e W = (Real.pi / 2) • W ∧
    compressionMap (Real.pi / 2) e W = 0 ∧
    fderiv Real (expCoordinates : EuclideanSpace Real (Fin 2) → Real × EuclideanSpace Real (Fin 2))
      ((Real.pi / 2) • e) W = (0, (2 / Real.pi) • W) ∧
    fderiv Real (fun Y => fullLog (productMap (Real.pi / 2) e Y)) 0 W = (0,0))


/-! ### Supporting lemmas -/

/-- For a unit vector the self inner product is one. -/
lemma inner_self_of_unit {e : V} (he : ‖e‖ = 1) : (inner Real e e : Real) = 1 := by
  rw [real_inner_self_eq_norm_sq, he, one_pow]

/-! ### The five requested results -/

/-- G1.  The sinc exponential of 7A.1 is Frechet differentiable at `r • e` for
`0 < r < π` and `‖e‖ = 1`, with derivative `expDerivative r e`.  The proof differentiates
the actual formula: away from the origin `expCoordinates` agrees with
`X ↦ (cos ‖X‖, (sin ‖X‖ / ‖X‖) • X)`, whose derivative is computed by the chain rule
from the derivative of the norm.  (The hypothesis `r < π` is part of the reviewed
statement; the argument itself only uses `0 < r`.) -/
theorem exp_derivative : GoalExpDerivative V := by
  intro r e hr _ he
  have hnX0 : ‖r • e‖ = r := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.le]
  have hX0ne : (r • e) ≠ 0 := by
    intro h; rw [h, norm_zero] at hnX0; exact hr.ne' hnX0.symm
  have hrne : r ≠ 0 := hr.ne'
  -- the norm is differentiable away from the origin
  have hn : HasFDerivAt (fun X : V => ‖X‖) (innerSL Real e) (r • e) := by
    have h := hasFDerivAt_norm_comp (f := fun X : V => X) (hasFDerivAt_id (r • e)) hX0ne
    refine h.congr_fderiv ?_
    ext W
    simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_id', id_eq, innerSL_apply_apply, smul_eq_mul, hnX0,
      real_inner_smul_left]
    field_simp
  -- the sinc profile, in its division form valid off the origin
  set d : Real := (Real.cos r * r - Real.sin r) / r ^ 2 with hd
  have hphi0 : HasDerivAt (fun t : Real => Real.sin t / t) d r := by
    have h := (Real.hasDerivAt_sin r).div (hasDerivAt_id r) hrne
    simp only [id_eq, mul_one] at h
    exact h
  have hphi : HasFDerivAt (fun X : V => Real.sin ‖X‖ / ‖X‖) (d • innerSL Real e) (r • e) := by
    have h0 : HasDerivAt (fun t : Real => Real.sin t / t) d ‖r • e‖ := by rw [hnX0]; exact hphi0
    exact h0.comp_hasFDerivAt _ hn
  have hcos : HasFDerivAt (fun X : V => Real.cos ‖X‖) ((-Real.sin r) • innerSL Real e) (r • e) := by
    have h0 : HasDerivAt Real.cos (-Real.sin r) ‖r • e‖ := by
      rw [hnX0]; exact Real.hasDerivAt_cos r
    exact h0.comp_hasFDerivAt _ hn
  have hvec : HasFDerivAt (fun X : V => (Real.sin ‖X‖ / ‖X‖) • X)
      ((Real.sin ‖r • e‖ / ‖r • e‖) • ContinuousLinearMap.id Real V +
        (d • innerSL Real e).smulRight (r • e)) (r • e) :=
    hphi.smul (hasFDerivAt_id (r • e))
  have hmain : HasFDerivAt (fun X : V => (Real.cos ‖X‖, (Real.sin ‖X‖ / ‖X‖) • X))
      (expDerivative r e) (r • e) := by
    refine (hcos.prodMk hvec).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun W => Prod.ext rfl ?_
    simp only [expDerivative, radialProjection, transverseProjection, hnX0,
      ContinuousLinearMap.prod_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, smul_eq_mul, hd]
    match_scalars <;> (field_simp; try ring)
  -- off the origin the sinc exponential agrees with its division form
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hX0ne] with X hX
  have hXne : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  simp [expCoordinates, Real.sinc_of_ne_zero hXne]

/-- G2.  On the branch `0 < r < π`, `‖e‖ = 1`, the maps `jacobiMap r e` and
`inverseJacobiMap r e` are two-sided inverses of each other; `r ≠ 0` and `sin r ≠ 0`
come from the stated domain. -/
theorem jacobi_inverse : GoalJacobiInverse V := by
  intro r e hr hrpi he
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hee : (inner Real e e : Real) = 1 := inner_self_of_unit he
  constructor <;>
  · ext W
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, jacobiMap, inverseJacobiMap,
      add_apply, smul_apply, radialProjection, transverseProjection,
      ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, inner_add_right, inner_smul_right, inner_sub_right, hee]
    match_scalars <;> (field_simp; try ring)

/-- G3.  Coordinate identities between the previously proved derivative maps:
`expDerivative = coordinateLift ∘ jacobiMap`, `productDerivative = coordinateLift ∘
compressionMap`, and `logDerivative ∘ coordinateLift = (0, inverseJacobiMap)`. -/
theorem coordinate_identities : GoalCoordinateIdentities V := by
  intro r e hr hrpi he
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hee : (inner Real e e : Real) = 1 := inner_self_of_unit he
  have hpy : Real.cos r ^ 2 + Real.sin r ^ 2 = 1 := Real.cos_sq_add_sin_sq r
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun W => Prod.ext ?_ ?_ <;>
    · simp only [expDerivative, coordinateLift, jacobiMap, radialProjection,
        transverseProjection, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.prod_apply, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
        innerSL_apply_apply, inner_add_right, inner_smul_right, inner_sub_right, hee,
        smul_eq_mul]
      first
        | ring1
        | (match_scalars <;> ring1)
  · refine ContinuousLinearMap.ext fun W => Prod.ext ?_ ?_ <;>
    · simp only [productDerivative, coordinateLift, compressionMap, radialProjection,
        transverseProjection, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.prod_apply, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
        innerSL_apply_apply, inner_add_right, inner_smul_right, inner_sub_right, hee,
        smul_eq_mul]
      first
        | ring1
        | (match_scalars <;> ring1)
  · refine ContinuousLinearMap.ext fun W => Prod.ext ?_ ?_ <;>
    · simp only [logDerivative, coordinateLift, inverseJacobiMap, ambientRadial,
        radialProjection, transverseProjection, ContinuousLinearMap.coe_comp,
        Function.comp_apply, ContinuousLinearMap.prod_apply, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        innerSL_apply_apply, inner_add_right, inner_smul_right, inner_sub_right, hee,
        smul_eq_mul, zero_apply]
      first
        | ring1
        | (match_scalars <;>
            first
              | ring1
              | linear_combination (inner Real e W : Real) * hpy)

/-- G4.  The actual composition `Y ↦ fullLog (productMap r e Y)` has Frechet derivative
`(0, inverseJacobiMap r e ∘ compressionMap r e)` at `0`.  This is 7A.2's
`composition_derivative` rewritten in the factorized form. -/
theorem composition_factorization : GoalCompositionFactorization V := by
  intro r e hr hrpi he
  have hs : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrpi
  have hee : (inner Real e e : Real) = 1 := inner_self_of_unit he
  refine (composition_derivative r e hr hrpi he).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun W => Prod.ext rfl ?_
  simp only [compositionDerivative, inverseJacobiMap, compressionMap, radialProjection,
    transverseProjection, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, inner_add_right, inner_smul_right, inner_sub_right, hee]
  match_scalars <;> (field_simp; try ring)

/-- G5.  Radial directions are fixed by `jacobiMap`, `inverseJacobiMap` and
`compressionMap`; and at `r = π / 2` the standard orthonormal pair of
`EuclideanSpace ℝ (Fin 2)` witnesses transverse actions `2 / π`, `π / 2` and `0`,
consistent with the actual Frechet derivatives supplied by G1 and G4 (the `fderiv`
values are read off from those `HasFDerivAt` statements). -/
theorem radial_and_equator : GoalRadialAndEquator := by
  constructor
  · intro r e _ _ he
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [jacobiMap, inverseJacobiMap, compressionMap, radialProjection,
        transverseProjection, he]
  · have hpi : (0 : Real) < Real.pi := Real.pi_pos
    have hpi2 : (0 : Real) < Real.pi / 2 := by positivity
    have hpi2' : Real.pi / 2 < Real.pi := by linarith
    have hsin : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have hcos : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    set e : EuclideanSpace Real (Fin 2) := EuclideanSpace.single 0 1 with hedef
    set W : EuclideanSpace Real (Fin 2) := EuclideanSpace.single 1 1 with hWdef
    have he : ‖e‖ = 1 := by simp [hedef]
    have hWn : ‖W‖ = 1 := by simp [hWdef]
    have hperp : (inner Real e W : Real) = 0 := by
      simp [hedef, hWdef, EuclideanSpace.inner_single_left]
    refine ⟨e, W, he, hWn, hperp, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [jacobiMap, radialProjection, transverseProjection, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
        innerSL_apply_apply, hperp, hsin, zero_smul, sub_zero, zero_add]
      match_scalars
      field_simp
    · simp only [inverseJacobiMap, radialProjection, transverseProjection, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
        innerSL_apply_apply, hperp, hsin, zero_smul, sub_zero, zero_add]
      match_scalars
      field_simp
    · simp only [compressionMap, radialProjection, transverseProjection,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hperp, hcos, zero_smul,
        add_zero]
    · have hd := exp_derivative (V := EuclideanSpace Real (Fin 2)) (Real.pi / 2) e hpi2 hpi2' he
      rw [hd.fderiv]
      refine Prod.ext ?_ ?_
      · simp [expDerivative, hperp]
      · simp only [expDerivative, radialProjection, transverseProjection,
          ContinuousLinearMap.prod_apply, smul_apply,
          ContinuousLinearMap.smulRight_apply, sub_apply, ContinuousLinearMap.id_apply,
          innerSL_apply_apply, hperp, hsin, hcos, zero_smul, sub_zero, zero_add]
        match_scalars
        field_simp
    · have hd := composition_factorization (V := EuclideanSpace Real (Fin 2)) (Real.pi / 2) e
        hpi2 hpi2' he
      rw [hd.fderiv]
      refine Prod.ext rfl ?_
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        compressionMap, inverseJacobiMap, radialProjection, transverseProjection, add_apply,
        smul_apply, ContinuousLinearMap.smulRight_apply, sub_apply,
        ContinuousLinearMap.id_apply, innerSL_apply_apply, hperp, hcos, zero_smul, sub_zero,
        smul_zero, inner_zero_right, add_zero]

end SphericalProofRequest7A3
