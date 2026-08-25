/-
Generic logarithmic sublattice and infinite convolution bridge.

The existing IFFT sublattice modules prove arbitrary-H support closure for
finite convolution series (IFFTSublatticeConvolution) and the exact
pointwise-log support / filter-annihilation for explicit divisor sublattices
(IFFTLogSublatticeBridge). This module supplies the missing normalized
product/convolution identities and the convergent infinite Taylor bridge, from
which the paper's arbitrary-H theorem and exact filter consequence follow.

Normalization guard: the paper's Fourier coefficients are NORMALIZED
(normalizedPositiveDFT f = (g:ℂ)⁻¹ * positiveDFT f). The convolution identities
below MUST use normalizedPositiveDFT; the 1/g factor is not optional.
-/
import RequestProject.IFFTLogSublatticeBridge

open scoped BigOperators

namespace ResidueSlices

noncomputable def logarithmicConvolutionCoeff (n : Nat) : Complex :=
  if n = 0 then 0 else (-1 : Complex) ^ (n + 1) / (n : Complex)

noncomputable def logarithmicConvolutionSpectrum
    {g : Nat} [NeZero g] (f : ZMod g → Complex) : ZMod g → Complex :=
  fun k => ∑' n : Nat,
    logarithmicConvolutionCoeff n * cyclicConvolutionPow f n k

/-- Character orthogonality on `ZMod g`. -/
private theorem sum_stdAddChar_orthogonality {g : ℕ} [NeZero g] (m : ZMod g) :
    ∑ a : ZMod g, (ZMod.stdAddChar (m * a) : ℂ) = if m = 0 then (g : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod g) (R' := ℂ) (ψ := ZMod.stdAddChar) m
    (ZMod.isPrimitive_stdAddChar g)
  simpa [mul_comm, ZMod.card] using h

theorem normalizedPositiveDFT_pointwise_mul
    {g : Nat} [NeZero g] (f h : ZMod g → Complex) :
    normalizedPositiveDFT (fun j => f j * h j) =
      cyclicConvolution (normalizedPositiveDFT f)
        (normalizedPositiveDFT h) := by
  funext k
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  have expand : ∀ a : ZMod g,
      normalizedPositiveDFT f a * normalizedPositiveDFT h (k - a) =
        ∑ j : ZMod g, ∑ l : ZMod g,
          ((g : ℂ)⁻¹ * (g : ℂ)⁻¹ * (f j * h l * ZMod.stdAddChar (l * k))) *
            ZMod.stdAddChar ((j - l) * a) := by
    intro a
    have hprod : ∀ j l : ZMod g,
        (ZMod.stdAddChar (j * a) : ℂ) * ZMod.stdAddChar (l * (k - a)) =
          ZMod.stdAddChar (l * k) * ZMod.stdAddChar ((j - l) * a) := by
      intro j l
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp only [normalizedPositiveDFT, positiveDFT]
    rw [show ((g : ℂ)⁻¹ * ∑ j : ZMod g, ZMod.stdAddChar (j * a) * f j) *
          ((g : ℂ)⁻¹ * ∑ l : ZMod g, ZMod.stdAddChar (l * (k - a)) * h l) =
        ((g : ℂ)⁻¹ * (g : ℂ)⁻¹) *
          ((∑ j : ZMod g, ZMod.stdAddChar (j * a) * f j) *
            (∑ l : ZMod g, ZMod.stdAddChar (l * (k - a)) * h l)) from by ring,
      Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (ZMod.stdAddChar (j * a) : ℂ) * f j *
          (ZMod.stdAddChar (l * (k - a)) * h l) =
        (f j * h l) * ((ZMod.stdAddChar (j * a) : ℂ) *
          ZMod.stdAddChar (l * (k - a))) from by ring, hprod j l]
    ring
  symm
  calc
    cyclicConvolution (normalizedPositiveDFT f) (normalizedPositiveDFT h) k
        = ∑ a : ZMod g, ∑ j : ZMod g, ∑ l : ZMod g,
            ((g : ℂ)⁻¹ * (g : ℂ)⁻¹ * (f j * h l * ZMod.stdAddChar (l * k))) *
              ZMod.stdAddChar ((j - l) * a) := by
          simp only [cyclicConvolution]
          exact Finset.sum_congr rfl fun a _ => expand a
    _ = ∑ j : ZMod g, ∑ l : ZMod g, ∑ a : ZMod g,
            ((g : ℂ)⁻¹ * (g : ℂ)⁻¹ * (f j * h l * ZMod.stdAddChar (l * k))) *
              ZMod.stdAddChar ((j - l) * a) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ j : ZMod g, ∑ l : ZMod g,
            ((g : ℂ)⁻¹ * (g : ℂ)⁻¹ * (f j * h l * ZMod.stdAddChar (l * k))) *
              (if j - l = 0 then (g : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← Finset.mul_sum, sum_stdAddChar_orthogonality]
    _ = ∑ j : ZMod g,
            ((g : ℂ)⁻¹ * (g : ℂ)⁻¹ * (f j * h j * ZMod.stdAddChar (j * k))) *
              (g : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j]
          · simp
          · intro l _ hl
            have : j - l ≠ 0 := by
              intro hzero
              exact hl (sub_eq_zero.mp hzero).symm
            rw [if_neg this, mul_zero]
          · intro hj
            exact absurd (Finset.mem_univ j) hj
    _ = normalizedPositiveDFT (fun j => f j * h j) k := by
          simp only [normalizedPositiveDFT, positiveDFT, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          field_simp

theorem normalizedPositiveDFT_pointwise_pow
    {g : Nat} [NeZero g] (f : ZMod g → Complex) (n : Nat) :
    normalizedPositiveDFT (fun j => f j ^ n) =
      cyclicConvolutionPow (normalizedPositiveDFT f) n := by
  induction n with
  | zero =>
      funext k
      have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
      have hsum : (∑ j : ZMod g, (ZMod.stdAddChar (j * k) : ℂ) * (1 : ℂ) ^ 0) =
          if k = 0 then (g : ℂ) else 0 := by
        rw [← sum_stdAddChar_orthogonality k]
        exact Finset.sum_congr rfl fun j _ => by rw [pow_zero, mul_one, mul_comm]
      show (g : ℂ)⁻¹ * positiveDFT (fun j => f j ^ 0) k = _
      simp only [positiveDFT, pow_zero, cyclicConvolutionPow]
      rw [show (∑ j : ZMod g, (ZMod.stdAddChar (j * k) : ℂ) * (1 : ℂ)) =
          ∑ j : ZMod g, (ZMod.stdAddChar (j * k) : ℂ) * (1 : ℂ) ^ 0 from by
        exact Finset.sum_congr rfl fun j _ => by rw [pow_zero], hsum]
      by_cases hk : k = 0
      · rw [if_pos hk, if_pos hk, inv_mul_cancel₀ hg]
      · rw [if_neg hk, if_neg hk, mul_zero]
  | succ n ih =>
      have hpow : (fun j => f j ^ (n + 1)) = (fun j => f j ^ n * f j) := by
        funext j
        ring
      rw [hpow, normalizedPositiveDFT_pointwise_mul, ih]
      rfl

/-- Linearity of the normalized transform over a finite scalar combination. -/
private theorem normalizedPositiveDFT_finset_sum
    {g : ℕ} [NeZero g] (s : Finset ℕ) (c : ℕ → ℂ) (F : ℕ → ZMod g → ℂ) (k : ZMod g) :
    normalizedPositiveDFT (fun j => ∑ n ∈ s, c n * F n j) k =
      ∑ n ∈ s, c n * normalizedPositiveDFT (F n) k := by
  simp only [normalizedPositiveDFT, positiveDFT, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => by ring

theorem normalizedPositiveDFT_truncatedLog
    {g : Nat} [NeZero g] (M : Nat) (e : ZMod g → Complex) :
    normalizedPositiveDFT
        (fun j => ∑ n ∈ Finset.range (M + 1),
          logarithmicConvolutionCoeff n * e j ^ n) =
      truncatedLogSpectrum M (normalizedPositiveDFT e) := by
  funext k
  rw [normalizedPositiveDFT_finset_sum (Finset.range (M + 1))
    logarithmicConvolutionCoeff (fun n j => e j ^ n) k]
  simp only [truncatedLogSpectrum, finiteConvolutionSeries]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← congrFun (normalizedPositiveDFT_pointwise_pow e n) k]
  rfl

/-- The Taylor series of `log (1 + z)` written with the module's coefficients. -/
private theorem hasSum_logarithmicConvolutionCoeff {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => logarithmicConvolutionCoeff n * z ^ n)
      (Complex.log (1 + z)) := by
  have h := Complex.hasSum_taylorSeries_log hz
  have hfun : (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * z ^ n / (n : ℂ)) =
      fun n : ℕ => logarithmicConvolutionCoeff n * z ^ n := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [logarithmicConvolutionCoeff]
    · rw [logarithmicConvolutionCoeff, if_neg hn]
      ring
  rwa [hfun] at h

private theorem hasSum_logarithmicConvolutionSpectrum
    {g : ℕ} [NeZero g] (e : ZMod g → ℂ) (he : ∀ j, ‖e j‖ < 1) (k : ZMod g) :
    HasSum (fun n : ℕ => logarithmicConvolutionCoeff n *
        cyclicConvolutionPow (normalizedPositiveDFT e) n k)
      (normalizedPositiveDFT (fun j => Complex.log (1 + e j)) k) := by
  have hrw : ∀ n : ℕ, logarithmicConvolutionCoeff n *
      cyclicConvolutionPow (normalizedPositiveDFT e) n k =
      ∑ j : ZMod g, ((g : ℂ)⁻¹ * ZMod.stdAddChar (j * k)) *
        (logarithmicConvolutionCoeff n * e j ^ n) := by
    intro n
    rw [← congrFun (normalizedPositiveDFT_pointwise_pow e n) k]
    simp only [normalizedPositiveDFT, positiveDFT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hval : normalizedPositiveDFT (fun j => Complex.log (1 + e j)) k =
      ∑ j : ZMod g, ((g : ℂ)⁻¹ * ZMod.stdAddChar (j * k)) *
        Complex.log (1 + e j) := by
    simp only [normalizedPositiveDFT, positiveDFT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hval]
  simp only [hrw]
  exact hasSum_sum fun j _ => (hasSum_logarithmicConvolutionCoeff (he j)).mul_left _

theorem summable_logarithmicConvolutionSpectrum
    {g : Nat} [NeZero g] (e : ZMod g → Complex)
    (he : ∀ j, norm (e j) < 1) (k : ZMod g) :
    Summable (fun n : Nat =>
      logarithmicConvolutionCoeff n *
        cyclicConvolutionPow (normalizedPositiveDFT e) n k) :=
  (hasSum_logarithmicConvolutionSpectrum e he k).summable

theorem normalizedPositiveDFT_log_one_add
    {g : Nat} [NeZero g] (e : ZMod g → Complex)
    (he : ∀ j, norm (e j) < 1) :
    normalizedPositiveDFT (fun j => Complex.log (1 + e j)) =
      logarithmicConvolutionSpectrum (normalizedPositiveDFT e) := by
  funext k
  exact ((hasSum_logarithmicConvolutionSpectrum e he k).tsum_eq).symm

theorem logarithmicConvolutionSpectrum_supported
    {g : Nat} [NeZero g] (H : AddSubgroup (ZMod g))
    (f : ZMod g → Complex)
    (hf : ∀ k, k ∉ H → f k = 0) :
    ∀ k, k ∉ H → logarithmicConvolutionSpectrum f k = 0 := by
  intro k hk
  have hzero : ∀ n : ℕ,
      logarithmicConvolutionCoeff n * cyclicConvolutionPow f n k = 0 := by
    intro n
    rw [cyclicConvolutionPow_supported H f hf n k hk, mul_zero]
  simp only [logarithmicConvolutionSpectrum, hzero, tsum_zero]

theorem normalizedPositiveDFT_log_one_add_supported
    {g : Nat} [NeZero g] (H : AddSubgroup (ZMod g))
    (e : ZMod g → Complex)
    (heNorm : ∀ j, norm (e j) < 1)
    (heSupport : ∀ k, k ∉ H → normalizedPositiveDFT e k = 0) :
    ∀ k, k ∉ H →
      normalizedPositiveDFT (fun j => Complex.log (1 + e j)) k = 0 := by
  intro k hk
  rw [congrFun (normalizedPositiveDFT_log_one_add e heNorm) k]
  exact logarithmicConvolutionSpectrum_supported H _ heSupport k hk

theorem packetFilterValue_eq_positive_at_neg
    {g : Nat} [NeZero g] (w : ZMod g → Complex) (k : ZMod g) :
    packetFilterValue w k =
      ∑ j : ZMod g, w j * ZMod.stdAddChar (j * (-k)) := by
  unfold packetFilterValue
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show -(k * j) = j * (-k) from by ring]

theorem logarithmic_estimator_annihilated_of_norm_lt_one
    {g : Nat} [NeZero g] (H : AddSubgroup (ZMod g))
    (e w : ZMod g → Complex)
    (heNorm : ∀ j, norm (e j) < 1)
    (heSupport : ∀ k, k ∉ H → normalizedPositiveDFT e k = 0)
    (hw : ∀ k, k ∈ H →
      (∑ j : ZMod g, w j * ZMod.stdAddChar (j * k)) = 0) :
    ∑ j : ZMod g, w j * Complex.log (1 + e j) = 0 := by
  let L : ZMod g → ℂ := fun j => Complex.log (1 + e j)
  calc
    (∑ j : ZMod g, w j * Complex.log (1 + e j)) =
        ∑ j : ZMod g, w j *
          (∑ k : ZMod g,
            normalizedPositiveDFT L k * ZMod.stdAddChar (-(k * j))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          change w j * L j = _
          rw [inverse_normalizedPositiveDFT L j]
    _ = ∑ k : ZMod g, normalizedPositiveDFT L k * packetFilterValue w k :=
      weighted_inverse_fourier_sum w (normalizedPositiveDFT L)
    _ = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k ∈ H
      · rw [packetFilterValue_eq_positive_at_neg, hw (-k) (H.neg_mem hk), mul_zero]
      · rw [normalizedPositiveDFT_log_one_add_supported H e heNorm heSupport k hk,
          zero_mul]

end ResidueSlices
