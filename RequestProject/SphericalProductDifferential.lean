import RequestProject.SpinFactorCrossNorm

/- Typed specification only. These Goal definitions are propositions, not proofs.
No claim is made here about a sphere connection, geodesic distance or Hessian. -/
namespace SphericalProofRequest7A1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]

noncomputable def expCoordinates (X : V) : Real × V :=
  (Real.cos ‖X‖, Real.sinc ‖X‖ • X)

noncomputable def basePoint (r : Real) (e : V) : Real × V :=
  (Real.cos r, Real.sin r • e)

noncomputable def productMap (r : Real) (e Y : V) : Real × V :=
  SpinFactor.mul (-(innerₗ V)) (basePoint r e) (expCoordinates Y)

noncomputable def euclideanSquare (p : Real × V) : Real :=
  p.1 ^ 2 + ‖p.2‖ ^ 2

noncomputable def scalarLog (p : Real × V) : Real :=
  Real.log (Real.sqrt (euclideanSquare p))

noncomputable def expDerivativeAtZero : V →L[Real] (Real × V) :=
  (0 : V →L[Real] Real).prod (ContinuousLinearMap.id Real V)

noncomputable def productDerivative (r : Real) (e : V) : V →L[Real] (Real × V) :=
  ((-Real.sin r) • innerSL Real e).prod
    ((Real.cos r) • ContinuousLinearMap.id Real V)

-- G1: origin, Euclidean unit quadric, and radial compatibility with the base point.
def GoalOriginAndUnit (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  expCoordinates (0 : V) = (1, 0) ∧
    (∀ X : V, euclideanSquare (expCoordinates X) = 1) ∧
      ∀ (r : Real) (e : V), 0 ≤ r → ‖e‖ = 1 →
        expCoordinates (r • e) = basePoint r e

-- G2: a full Frechet derivative, not merely directional derivatives.
def GoalExpDerivative (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  HasFDerivAt (expCoordinates : V → Real × V) expDerivativeAtZero 0

-- G3: differentiate the existing product composed with the actual exponential formula.
def GoalProductDerivative (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    HasFDerivAt (productMap r e) (productDerivative r e) 0

-- G4: the scalar logarithm is part of the full shadow logarithm and must be checked.
def GoalScalarLogDerivative (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e : V), 0 < r → r < Real.pi → ‖e‖ = 1 →
    HasFDerivAt (fun Y : V => scalarLog (productMap r e Y)) (0 : V →L[Real] Real) 0

-- G5: explicit tangent equation for the actual derivative, not a manifold identification.
def GoalTangency (V : Type*) [NormedAddCommGroup V] [InnerProductSpace Real V] : Prop :=
  ∀ (r : Real) (e W : V),
    Real.cos r * (productDerivative r e W).1 +
      inner Real (Real.sin r • e) (productDerivative r e W).2 = 0

-- G6: nonzero perpendicular directions really exist and collapse at the equator.
def GoalEquatorWitness : Prop :=
  ∃ e w : EuclideanSpace Real (Fin 2),
    ‖e‖ = 1 ∧ ‖w‖ = 1 ∧ inner Real e w = 0 ∧
      productDerivative (Real.pi / 2) e w = (0, 0)

/-! ### Supporting lemmas -/

/-- `sinc t * t = sin t`, including at `t = 0`. -/
private lemma sinc_mul_self (t : Real) : Real.sinc t * t = Real.sin t := by
  by_cases h : t = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h, div_mul_cancel₀ _ h]

/-- The elementary quadratic bound `|cos t - 1| ≤ t ^ 2 / 2`. -/
private lemma abs_cos_sub_one_le (t : Real) : |Real.cos t - 1| ≤ t ^ 2 / 2 := by
  have h1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have h2 : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
  rw [abs_le]
  constructor <;> linarith

/-- The scalar part of the exponential coordinates has vanishing derivative at the origin. -/
private lemma hasFDerivAt_cos_norm :
    HasFDerivAt (fun Y : V => Real.cos ‖Y‖) (0 : V →L[Real] Real) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, norm_zero, Real.cos_zero, zero_apply, sub_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : V) (by positivity : (0 : Real) < 2 * ε)] with Y hY
  have hY' : ‖Y‖ < 2 * ε := by simpa [dist_eq_norm] using hY
  have h0 : (0 : Real) ≤ ‖Y‖ := norm_nonneg Y
  calc ‖Real.cos ‖Y‖ - 1‖ = |Real.cos ‖Y‖ - 1| := rfl
    _ ≤ ‖Y‖ ^ 2 / 2 := abs_cos_sub_one_le _
    _ ≤ ε * ‖Y‖ := by nlinarith

/-- The vector part of the exponential coordinates has derivative the identity at the origin. -/
private lemma hasFDerivAt_sinc_smul :
    HasFDerivAt (fun Y : V => Real.sinc ‖Y‖ • Y) (ContinuousLinearMap.id Real V) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, norm_zero, Real.sinc_zero, smul_zero, sub_zero,
    ContinuousLinearMap.id_apply]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hcont : ContinuousAt (fun Y : V => Real.sinc ‖Y‖) 0 :=
    (Real.continuous_sinc.comp continuous_norm).continuousAt
  have hlim : Filter.Tendsto (fun Y : V => Real.sinc ‖Y‖) (nhds 0) (nhds 1) := by
    have h := hcont.tendsto
    simpa using h
  have hev : ∀ᶠ Y : V in nhds 0, |Real.sinc ‖Y‖ - 1| ≤ ε := by
    have := (Metric.tendsto_nhds.mp hlim) ε hε
    filter_upwards [this] with Y hY
    exact le_of_lt (by simpa [Real.dist_eq] using hY)
  filter_upwards [hev] with Y hY
  have : ‖Real.sinc ‖Y‖ • Y - Y‖ = |Real.sinc ‖Y‖ - 1| * ‖Y‖ := by
    rw [show Real.sinc ‖Y‖ • Y - Y = (Real.sinc ‖Y‖ - 1) • Y by module, norm_smul]
    simp [Real.norm_eq_abs]
  rw [this]
  exact mul_le_mul_of_nonneg_right hY (norm_nonneg Y)

/-- Left multiplication by the base point in the spin-factor product, as a continuous
linear map on the coordinate space `ℝ × V`. -/
private noncomputable def leftMulCLM (r : Real) (e : V) : (Real × V) →L[Real] (Real × V) :=
  (((Real.cos r) • ContinuousLinearMap.fst Real Real V) -
      (innerSL Real (Real.sin r • e)).comp (ContinuousLinearMap.snd Real Real V)).prod
    (((Real.cos r) • ContinuousLinearMap.snd Real Real V) +
      (ContinuousLinearMap.fst Real Real V).smulRight (Real.sin r • e))

private lemma leftMulCLM_apply (r : Real) (e : V) (p : Real × V) :
    leftMulCLM r e p = SpinFactor.mul (-(innerₗ V)) (basePoint r e) p := by
  simp [leftMulCLM, SpinFactor.mul, basePoint, sub_eq_add_neg, smul_smul, mul_comm]

/-! ### The six requested results -/

theorem origin_and_unit : GoalOriginAndUnit V := by
  refine ⟨by simp [expCoordinates], ?_, ?_⟩
  · intro X
    have hnorm : ‖Real.sinc ‖X‖ • X‖ = |Real.sinc ‖X‖| * ‖X‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have hsq : ‖Real.sinc ‖X‖ • X‖ ^ 2 = Real.sin ‖X‖ ^ 2 := by
      rw [hnorm, mul_pow, sq_abs, ← mul_pow, sinc_mul_self]
    simp only [euclideanSquare, expCoordinates, hsq]
    exact Real.cos_sq_add_sin_sq _
  · intro r e hr he
    have hnorm : ‖r • e‖ = r := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
    simp only [expCoordinates, basePoint, hnorm, smul_smul, sinc_mul_self]

theorem exp_derivative_zero : GoalExpDerivative V :=
  HasFDerivAt.prodMk (hasFDerivAt_cos_norm (V := V)) (hasFDerivAt_sinc_smul (V := V))

theorem product_derivative : GoalProductDerivative V := by
  intro r e _ _ _
  have hcomp :
      HasFDerivAt (fun Y : V => leftMulCLM r e (expCoordinates Y))
        ((leftMulCLM r e).comp (expDerivativeAtZero (V := V))) 0 :=
    (leftMulCLM r e).hasFDerivAt.comp 0 (exp_derivative_zero (V := V))
  have hfun : (fun Y : V => leftMulCLM r e (expCoordinates Y)) = productMap r e := by
    funext Y
    rw [leftMulCLM_apply]
    rfl
  have hderiv : (leftMulCLM r e).comp (expDerivativeAtZero (V := V)) = productDerivative r e := by
    ext W <;>
      simp [leftMulCLM, expDerivativeAtZero, productDerivative]
  rw [hfun, hderiv] at hcomp
  exact hcomp

/-- The product map sends the origin to the base point. -/
private lemma productMap_zero (r : Real) (e : V) : productMap r e 0 = basePoint r e := by
  simp [productMap, expCoordinates, SpinFactor.mul, basePoint]

/-- The Euclidean square of the product map equals one at the origin, for unit `e`. -/
private lemma euclideanSquare_productMap_zero (r : Real) (e : V) (he : ‖e‖ = 1) :
    euclideanSquare (productMap r e 0) = 1 := by
  rw [productMap_zero]
  have : ‖Real.sin r • e‖ ^ 2 = Real.sin r ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs]
  simp only [euclideanSquare, basePoint, this]
  exact Real.cos_sq_add_sin_sq _

theorem scalar_log_derivative : GoalScalarLogDerivative V := by
  intro r e hr hrpi he
  have hf : HasFDerivAt (productMap r e) (productDerivative r e) 0 :=
    product_derivative r e hr hrpi he
  have h1 : HasFDerivAt (fun Y : V => (productMap r e Y).1)
      ((ContinuousLinearMap.fst Real Real V).comp (productDerivative r e)) 0 := hf.fst
  have h2 : HasFDerivAt (fun Y : V => (productMap r e Y).2)
      ((ContinuousLinearMap.snd Real Real V).comp (productDerivative r e)) 0 := hf.snd
  -- the Euclidean square along the product map has vanishing derivative at the origin
  have hq : HasFDerivAt (fun Y : V => euclideanSquare (productMap r e Y))
      (0 : V →L[Real] Real) 0 := by
    refine ((h1.pow 2).add h2.norm_sq).congr_fderiv ?_
    ext W
    simp [productMap_zero, basePoint, productDerivative, innerSL_apply_apply]
    ring
  -- the value at the origin is 1, so sqrt and log are differentiable there
  have hval : euclideanSquare (productMap r e 0) = 1 := euclideanSquare_productMap_zero r e he
  have hsqrt : HasDerivAt Real.sqrt ((2 : Real)⁻¹) 1 := by
    have := Real.hasDerivAt_sqrt (x := (1 : Real)) one_ne_zero
    simpa using this
  have hlog : HasDerivAt Real.log ((1 : Real)⁻¹) (Real.sqrt 1) := by
    rw [Real.sqrt_one]
    exact Real.hasDerivAt_log one_ne_zero
  have hcomp : HasDerivAt (fun t : Real => Real.log (Real.sqrt t))
      ((1 : Real)⁻¹ * (2 : Real)⁻¹) 1 := hlog.comp (1 : Real) hsqrt
  have hcomp' : HasDerivAt (fun t : Real => Real.log (Real.sqrt t))
      ((1 : Real)⁻¹ * (2 : Real)⁻¹) (euclideanSquare (productMap r e 0)) := by
    rw [hval]; exact hcomp
  have hfinal := hcomp'.comp_hasFDerivAt (0 : V) hq
  have hfinal2 : HasFDerivAt (fun Y : V => scalarLog (productMap r e Y))
      (((1 : Real)⁻¹ * (2 : Real)⁻¹) • (0 : V →L[Real] Real)) 0 := hfinal
  simpa using hfinal2

theorem product_tangency : GoalTangency V := by
  intro r e W
  simp only [productDerivative, ContinuousLinearMap.prod_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply, real_inner_smul_left,
    real_inner_smul_right, smul_eq_mul]
  ring

theorem equator_witness : GoalEquatorWitness := by
  refine ⟨EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp [EuclideanSpace.inner_single_left]
  · have hperp : inner Real (EuclideanSpace.single (0 : Fin 2) (1 : Real))
        (EuclideanSpace.single (1 : Fin 2) (1 : Real)) = 0 := by
      simp [EuclideanSpace.inner_single_left]
    ext <;>
      simp [productDerivative, innerSL_apply_apply, hperp, Real.cos_pi_div_two]

end SphericalProofRequest7A1
