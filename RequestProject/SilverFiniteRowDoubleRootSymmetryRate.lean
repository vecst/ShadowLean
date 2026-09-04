/-
Cubic-silver finite-row crossover, Phase B4B11: complete critical symmetry-defect
upper bound at the genuine center-error inner scale.
-/
import RequestProject.SilverFiniteRowDoubleRootCurvatureRate

open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

/-- The double-root inner scale determined by the magnitude of the center error. -/
noncomputable def centerInnerScale (N : Nat) (alpha : Real) : Real :=
  Real.sqrt (|centerError N alpha| / alpha)

/-- The complete critical endpoint-symmetry defect at the center-error inner scale. -/
noncomputable def centerCriticalSymmetryDefect
    (N : Nat) (alpha : Real) : Real :=
  criticalEndpointSymmetryDefect alpha (centerInnerScale N alpha)
    (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)

theorem centerInnerScale_nonneg (N : Nat) (alpha : Real) :
    0 <= centerInnerScale N alpha := by
  exact Real.sqrt_nonneg _

theorem centerInnerScale_sq
    (N : Nat) {alpha : Real} (halpha : 0 < alpha) :
    centerInnerScale N alpha ^ 2 = |centerError N alpha| / alpha := by
  unfold centerInnerScale
  exact Real.sq_sqrt (div_nonneg (abs_nonneg _) halpha.le)

theorem centerInnerScale_pos_of_centerError_neg
    (N : Nat) {alpha : Real} (halpha : 0 < alpha)
    (herror : centerError N alpha < 0) :
    0 < centerInnerScale N alpha := by
  unfold centerInnerScale
  exact Real.sqrt_pos.mpr (div_pos (abs_pos.mpr (ne_of_lt herror)) halpha)

theorem centerError_eq_neg_alpha_mul_centerInnerScale_sq_of_neg
    (N : Nat) {alpha : Real} (halpha : 0 < alpha)
    (herror : centerError N alpha < 0) :
    centerError N alpha = -alpha * centerInnerScale N alpha ^ 2 := by
  rw [centerInnerScale_sq N halpha, abs_of_neg herror]
  field_simp

theorem abs_criticalEndpointSymmetryDefect_le
    (alpha t derivativeError curvatureDefect : Real) :
    |criticalEndpointSymmetryDefect alpha t derivativeError curvatureDefect| <=
      2 * |derivativeError| ^ 2 +
        16 * t ^ 2 * |derivativeError| +
        8 * t ^ 2 * |derivativeError| ^ 2 +
        32 * t ^ 4 +
        4 * |alpha| * t ^ 2 * |curvatureDefect| * (1 + 4 * t ^ 2) := by
  unfold criticalEndpointSymmetryDefect
  have ht2 : (0 : Real) ≤ t ^ 2 := sq_nonneg t
  have ht4 : (0 : Real) ≤ t ^ 4 := by positivity
  have hp : (0 : Real) ≤ t ^ 2 * (1 + 4 * t ^ 2) := by positivity
  have hsq : derivativeError ^ 2 = |derivativeError| ^ 2 := (sq_abs _).symm
  have hac : alpha * curvatureDefect ≤ |alpha| * |curvatureDefect| := by
    rw [← abs_mul]; exact le_abs_self _
  have hac' : -(|alpha| * |curvatureDefect|) ≤ alpha * curvatureDefect := by
    rw [← abs_mul]; exact neg_abs_le _
  have h1 := mul_le_mul_of_nonneg_right hac hp
  have h2 := mul_le_mul_of_nonneg_right hac' hp
  have h3 := mul_le_mul_of_nonneg_left (le_abs_self derivativeError) ht2
  have h4 := mul_le_mul_of_nonneg_left (neg_abs_le derivativeError) ht2
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg derivativeError, abs_nonneg alpha,
    abs_nonneg curvatureDefect, mul_nonneg ht2 (abs_nonneg derivativeError)]

theorem eventually_centerDerivativeError_geometric_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in Filter.atTop,
        |centerDerivativeError N alpha| ≤
          C * (((N + 1 : Nat) : Real) * centerRho alpha ^ N) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, _hrho1⟩ := centerRho_mem_unitInterval halpha0
  set K : Real := ‖centerDerivativeChannelCoefficient alpha‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨2 * alpha * K + 1, by positivity, ?_⟩
  have habs : Filter.Tendsto
      (fun N : Nat =>
        |(centerDerivativeError N alpha - centerDerivativeLeadingTerm N alpha) /
          ((N : Real) * centerRho alpha ^ N)|)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_centerDerivativeError_sub_leading_normalized halpha).abs
  have hev : ∀ᶠ N : Nat in Filter.atTop,
      |(centerDerivativeError N alpha - centerDerivativeLeadingTerm N alpha) /
        ((N : Real) * centerRho alpha ^ N)| < 1 :=
    habs.eventually_lt_const (by norm_num)
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with N hN1 hN
  have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hpow : (0 : Real) < centerRho alpha ^ N := pow_pos hrho0 N
  have hden : (0 : Real) < (N : Real) * centerRho alpha ^ N := by positivity
  have hL : |centerDerivativeLeadingTerm N alpha| ≤
      2 * alpha * K * ((N : Real) * centerRho alpha ^ N) := by
    have hnorm : ‖centerDerivativeChannelCoefficient alpha *
        centerUnitChannel alpha ^ N‖ = K := by
      rw [hK, norm_mul, norm_pow, norm_centerUnitChannel halpha0, one_pow, mul_one]
    have hre : |Complex.re (centerDerivativeChannelCoefficient alpha *
        centerUnitChannel alpha ^ N)| ≤ K := by
      rw [← hnorm]; exact Complex.abs_re_le_norm _
    have heq := centerDerivativeLeadingTerm_normalized hN halpha0
    have hexp : centerDerivativeLeadingTerm N alpha =
        (2 * alpha * Complex.re (centerDerivativeChannelCoefficient alpha *
          centerUnitChannel alpha ^ N)) * ((N : Real) * centerRho alpha ^ N) :=
      (div_eq_iff (ne_of_gt hden)).mp heq
    rw [hexp, abs_mul, abs_of_pos hden]
    refine mul_le_mul_of_nonneg_right ?_ hden.le
    rw [abs_mul, abs_of_pos (by linarith : (0 : Real) < 2 * alpha)]
    exact mul_le_mul_of_nonneg_left hre (by linarith)
  have hrem : |centerDerivativeError N alpha - centerDerivativeLeadingTerm N alpha| ≤
      (N : Real) * centerRho alpha ^ N := by
    rw [abs_div, abs_of_pos hden, div_lt_one hden] at hN1
    exact hN1.le
  have hmono : (N : Real) ≤ ((N + 1 : Nat) : Real) := by push_cast; linarith
  calc |centerDerivativeError N alpha|
      ≤ |centerDerivativeLeadingTerm N alpha| +
          |centerDerivativeError N alpha - centerDerivativeLeadingTerm N alpha| := by
        have h := abs_add_le (centerDerivativeLeadingTerm N alpha)
          (centerDerivativeError N alpha - centerDerivativeLeadingTerm N alpha)
        simpa using h
    _ ≤ 2 * alpha * K * ((N : Real) * centerRho alpha ^ N) +
          (N : Real) * centerRho alpha ^ N := add_le_add hL hrem
    _ = (2 * alpha * K + 1) * ((N : Real) * centerRho alpha ^ N) := by ring
    _ ≤ (2 * alpha * K + 1) * (((N + 1 : Nat) : Real) * centerRho alpha ^ N) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hmono hpow.le

theorem eventually_centerInnerScale_sq_geometric_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in Filter.atTop,
        centerInnerScale N alpha ^ 2 ≤ C * centerRho alpha ^ N := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨CE, hCE0, N0, hN0⟩ := centerError_geometric_upper halpha
  refine ⟨CE / alpha, by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N0, fun N hN => ?_⟩
  have hbound := hN0 N hN
  rw [centerInnerScale_sq N halpha0, div_le_iff₀ halpha0]
  have hEq : CE / alpha * centerRho alpha ^ N * alpha = CE * centerRho alpha ^ N := by
    field_simp
  rw [hEq]
  exact hbound

/-- Packaging of the five symmetry-defect summands into a single
`(N+1)^2 * rho^(2N)` geometric rate. -/
private theorem symmetryDefect_five_term_packaging
    {n r t2 D Q Cd Ct Cq a : Real}
    (hn : 1 ≤ n) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (ht2 : 0 ≤ t2) (hD : 0 ≤ D) (hQ : 0 ≤ Q) (ha : 0 < a)
    (hCd : 0 < Cd) (hCt : 0 < Ct) (hCq : 0 < Cq)
    (hDb : D ≤ Cd * (n * r)) (htb : t2 ≤ Ct * r) (hQb : Q ≤ Cq * (n ^ 2 * r)) :
    2 * D ^ 2 + 16 * t2 * D + 8 * t2 * D ^ 2 + 32 * t2 ^ 2 +
        4 * a * t2 * Q * (1 + 4 * t2)
      ≤ (2 * Cd ^ 2 + 16 * Ct * Cd + 8 * Ct * Cd ^ 2 + 32 * Ct ^ 2 +
          4 * a * Ct * Cq * (1 + 4 * Ct)) * (n ^ 2 * r ^ 2) := by
  have hn0 : (0 : Real) ≤ n := le_trans zero_le_one hn
  have hnn : n ≤ n ^ 2 := by nlinarith
  have hn2 : (1 : Real) ≤ n ^ 2 := by nlinarith
  have hr2 : (0 : Real) < r ^ 2 := by positivity
  have hD2 : D ^ 2 ≤ Cd ^ 2 * (n ^ 2 * r ^ 2) := by nlinarith
  have hb1 : 2 * D ^ 2 ≤ 2 * Cd ^ 2 * (n ^ 2 * r ^ 2) := by nlinarith
  have hb2 : 16 * t2 * D ≤ 16 * Ct * Cd * (n ^ 2 * r ^ 2) := by
    have e2 : t2 * D ≤ (Ct * r) * (Cd * (n * r)) :=
      mul_le_mul htb hDb hD (by positivity)
    have e2' : Ct * Cd * n * r ^ 2 ≤ Ct * Cd * n ^ 2 * r ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hCt.le hCd.le) hr2.le)
        (sub_nonneg.mpr hnn)]
    nlinarith [e2, e2']
  have hb3 : 8 * t2 * D ^ 2 ≤ 8 * Ct * Cd ^ 2 * (n ^ 2 * r ^ 2) := by
    have e3 : t2 * D ^ 2 ≤ (Ct * r) * (Cd ^ 2 * (n ^ 2 * r ^ 2)) :=
      mul_le_mul htb hD2 (sq_nonneg D) (by positivity)
    have e3' : (0 : Real) ≤ Ct * Cd ^ 2 * n ^ 2 * r ^ 2 * (1 - r) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCt.le (sq_nonneg Cd))
        (sq_nonneg n)) (sq_nonneg r)) (sub_nonneg.mpr hr1)
    nlinarith [e3, e3']
  have hb4 : 32 * t2 ^ 2 ≤ 32 * Ct ^ 2 * (n ^ 2 * r ^ 2) := by
    have e4 : t2 ^ 2 ≤ (Ct * r) ^ 2 := by nlinarith
    have e4' : (0 : Real) ≤ Ct ^ 2 * r ^ 2 * (n ^ 2 - 1) :=
      mul_nonneg (mul_nonneg (sq_nonneg Ct) (sq_nonneg r)) (sub_nonneg.mpr hn2)
    nlinarith [e4, e4']
  have hb5 : 4 * a * t2 * Q * (1 + 4 * t2) ≤
      4 * a * Ct * Cq * (1 + 4 * Ct) * (n ^ 2 * r ^ 2) := by
    have e5 : t2 * Q ≤ Ct * Cq * (n ^ 2 * r ^ 2) := by
      have h := mul_le_mul htb hQb hQ (by positivity : (0 : Real) ≤ Ct * r)
      nlinarith [h]
    have e5b : 1 + 4 * t2 ≤ 1 + 4 * Ct := by nlinarith
    have hmul := mul_le_mul e5 e5b (by linarith : (0 : Real) ≤ 1 + 4 * t2)
      (by positivity : (0 : Real) ≤ Ct * Cq * (n ^ 2 * r ^ 2))
    have hscale := mul_le_mul_of_nonneg_left hmul
      (by positivity : (0 : Real) ≤ 4 * a)
    nlinarith [hscale]
  linarith [hb1, hb2, hb3, hb4, hb5]

theorem eventually_centerCriticalSymmetryDefect_geometric_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in Filter.atTop,
        |centerCriticalSymmetryDefect N alpha| ≤
          C * (((N + 1 : Nat) : Real) ^ 2 *
            centerRho alpha ^ (2 * N)) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  obtain ⟨Cd, hCd0, hevd⟩ := eventually_centerDerivativeError_geometric_upper halpha
  obtain ⟨Ct, hCt0, hevt⟩ := eventually_centerInnerScale_sq_geometric_upper halpha
  obtain ⟨Cq, hCq0, hevq⟩ := eventually_centerCurvatureDefect_geometric_upper halpha
  refine ⟨2 * Cd ^ 2 + 16 * Ct * Cd + 8 * Ct * Cd ^ 2 + 32 * Ct ^ 2 +
    4 * alpha * Ct * Cq * (1 + 4 * Ct), by positivity, ?_⟩
  filter_upwards [hevd, hevt, hevq] with N hd ht hq
  have hn : (1 : Real) ≤ ((N + 1 : Nat) : Real) := by
    push_cast
    have : (0 : Real) ≤ (N : Real) := Nat.cast_nonneg N
    linarith
  have hrpow : (0 : Real) < centerRho alpha ^ N := pow_pos hrho0 N
  have hrle : centerRho alpha ^ N ≤ 1 := pow_le_one₀ hrho0.le hrho1.le
  have hkey := abs_criticalEndpointSymmetryDefect_le alpha (centerInnerScale N alpha)
    (centerDerivativeError N alpha) (centerCurvatureDefect N alpha)
  rw [abs_of_pos halpha0] at hkey
  have hpack := symmetryDefect_five_term_packaging
    (n := ((N + 1 : Nat) : Real)) (r := centerRho alpha ^ N)
    (t2 := centerInnerScale N alpha ^ 2) (D := |centerDerivativeError N alpha|)
    (Q := |centerCurvatureDefect N alpha|) (a := alpha)
    hn hrpow hrle (sq_nonneg _) (abs_nonneg _) (abs_nonneg _) halpha0
    hCd0 hCt0 hCq0 hd ht hq
  have hrr : centerRho alpha ^ (2 * N) = (centerRho alpha ^ N) ^ 2 := by
    rw [mul_comm, pow_mul]
  rw [hrr]
  unfold centerCriticalSymmetryDefect
  linarith [hkey, hpack]

/-- Polynomial-times-geometric domination with a squared polynomial factor. -/
private theorem tendsto_natSucc_sq_mul_pow_aux {x : Real} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (fun N : Nat => ((N + 1 : Nat) : Real) ^ 2 * x ^ N) atTop (nhds 0) := by
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hy1 : Real.sqrt x < 1 := by
    have := Real.sqrt_lt_sqrt hx0 hx1
    simpa using this
  have h := tendsto_natSucc_mul_pow hy0 hy1
  have h2 := h.mul h
  rw [mul_zero] at h2
  refine h2.congr ?_
  intro N
  have hsq : Real.sqrt x ^ N * Real.sqrt x ^ N = x ^ N := by
    rw [← mul_pow, Real.mul_self_sqrt hx0]
  calc ((N + 1 : Nat) : Real) * Real.sqrt x ^ N *
        (((N + 1 : Nat) : Real) * Real.sqrt x ^ N)
      = ((N + 1 : Nat) : Real) ^ 2 * (Real.sqrt x ^ N * Real.sqrt x ^ N) := by ring
    _ = ((N + 1 : Nat) : Real) ^ 2 * x ^ N := by rw [hsq]

theorem tendsto_centerCriticalSymmetryDefect
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto (fun N : Nat => centerCriticalSymmetryDefect N alpha)
      Filter.atTop (nhds 0) := by
  have halpha0 : 0 < alpha := lt_trans one_pos halpha
  obtain ⟨hrho0, hrho1⟩ := centerRho_mem_unitInterval halpha0
  obtain ⟨C, hC0, hev⟩ := eventually_centerCriticalSymmetryDefect_geometric_upper halpha
  have hbase0 : (0 : Real) ≤ centerRho alpha ^ 2 := sq_nonneg _
  have hbase1 : centerRho alpha ^ 2 < 1 := by nlinarith
  have hlim : Filter.Tendsto
      (fun N : Nat => C * (((N + 1 : Nat) : Real) ^ 2 * centerRho alpha ^ (2 * N)))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_natSucc_sq_mul_pow_aux hbase0 hbase1).const_mul C
    rw [mul_zero] at h
    refine h.congr (fun N => ?_)
    rw [pow_mul]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hev] with N hN
  simpa [Real.norm_eq_abs] using hN

theorem eventually_adaptiveDerivativeRow_centerCriticalSymmetryDefect_geometric_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N : Nat in Filter.atTop,
        |centerCriticalSymmetryDefect (adaptiveDerivativeRow N alpha) alpha| ≤
          C *
            ((((adaptiveDerivativeRow N alpha) + 1 : Nat) : Real) ^ 2 *
              centerRho alpha ^ (2 * adaptiveDerivativeRow N alpha)) := by
  obtain ⟨C, hC0, hev⟩ := eventually_centerCriticalSymmetryDefect_geometric_upper halpha
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨C, hC0, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N0, fun N hN => ?_⟩
  exact hN0 (adaptiveDerivativeRow N alpha)
    (le_trans hN (le_adaptiveDerivativeRow N alpha))

theorem tendsto_adaptiveDerivativeRow_centerCriticalSymmetryDefect
    {alpha : Real} (halpha : 1 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        centerCriticalSymmetryDefect (adaptiveDerivativeRow N alpha) alpha)
      Filter.atTop (nhds 0) := by
  have h := (tendsto_centerCriticalSymmetryDefect halpha).comp
    (tendsto_adaptiveDerivativeRow alpha)
  simpa [Function.comp_def] using h

end SilverFiniteRow
