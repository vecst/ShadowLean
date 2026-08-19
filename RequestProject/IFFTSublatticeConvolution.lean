/-
Sublattice convolution closure on `ZMod g`
(Phase 1B of the shadow packetization companions).

This file develops the finite group-algebra facts behind the paper's sublattice
convolution lemma: cyclic convolution of two functions supported in an additive
subgroup `H ≤ ZMod g` is again supported in `H`, hence so is every finite
convolution power (including the zeroth, the delta mass at `0`), every finite
scalar series in those powers with arbitrary complex coefficients, and in
particular the finite (algebraic) logarithmic series `truncatedLogSpectrum`.

Scope of this phase: finite support closure only.  Nothing here asserts
convergence of any series, identifies `truncatedLogSpectrum` with a pointwise
complex logarithm, or provides a Fourier-limit bridge.  The flagship theorem
merely composes the Phase 1A projection support statement with this finite
nonlinear closure; it does not claim that an unprojected generic packet is
supported in a proper subgroup.
-/
import RequestProject.IFFTSublatticeProjector

open scoped BigOperators

namespace ResidueSlices

/-- Cyclic (group-algebra) convolution on `ZMod g`. -/
noncomputable def cyclicConvolution {g : ℕ} [NeZero g]
    (f h : ZMod g → ℂ) : ZMod g → ℂ :=
  fun k => ∑ a : ZMod g, f a * h (k - a)

/-- Convolution powers; the zeroth power is the delta mass at `0`. -/
noncomputable def cyclicConvolutionPow {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) : ℕ → ZMod g → ℂ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => cyclicConvolution (cyclicConvolutionPow f n) f

/-- Finite scalar series in convolution powers, with arbitrary coefficients. -/
noncomputable def finiteConvolutionSeries {g : ℕ} [NeZero g]
    (coeff : ℕ → ℂ) (M : ℕ) (f : ZMod g → ℂ) : ZMod g → ℂ :=
  fun k => ∑ n ∈ Finset.range M, coeff n * cyclicConvolutionPow f n k

/-- Algebraic finite logarithmic series in convolution powers only. -/
noncomputable def truncatedLogSpectrum {g : ℕ} [NeZero g]
    (M : ℕ) (f : ZMod g → ℂ) : ZMod g → ℂ :=
  finiteConvolutionSeries
    (fun n => if n = 0 then 0 else (-1 : ℂ) ^ (n + 1) / (n : ℂ))
    (M + 1) f

/-- Convolution of two functions supported in a subgroup `H` is supported in `H`. -/
theorem cyclicConvolution_supported
    {g : ℕ} [NeZero g] (H : AddSubgroup (ZMod g))
    (f h : ZMod g → ℂ)
    (hf : ∀ k, k ∉ H → f k = 0)
    (hh : ∀ k, k ∉ H → h k = 0) :
    ∀ k, k ∉ H → cyclicConvolution f h k = 0 := by
  intro k hk
  refine Finset.sum_eq_zero ?_
  intro a _
  by_cases ha : a ∈ H
  · have hka : k - a ∉ H := by
      intro hmem
      exact hk (by simpa using H.add_mem hmem ha)
    rw [hh _ hka, mul_zero]
  · rw [hf _ ha, zero_mul]

/-- Every finite convolution power of a function supported in `H` (including the
zeroth power, the delta mass at `0`) is supported in `H`. -/
theorem cyclicConvolutionPow_supported
    {g : ℕ} [NeZero g] (H : AddSubgroup (ZMod g))
    (f : ZMod g → ℂ) (hf : ∀ k, k ∉ H → f k = 0) :
    ∀ n k, k ∉ H → cyclicConvolutionPow f n k = 0 := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k ≠ 0 := by
        intro h0
        exact hk (h0 ▸ H.zero_mem)
      simp [cyclicConvolutionPow, hk0]
  | succ n ih =>
      intro k hk
      exact cyclicConvolution_supported H _ f ih hf k hk

/-- Any finite scalar series in convolution powers stays supported in `H`. -/
theorem finiteConvolutionSeries_supported
    {g : ℕ} [NeZero g] (H : AddSubgroup (ZMod g))
    (coeff : ℕ → ℂ) (M : ℕ) (f : ZMod g → ℂ)
    (hf : ∀ k, k ∉ H → f k = 0) :
    ∀ k, k ∉ H → finiteConvolutionSeries coeff M f k = 0 := by
  intro k hk
  refine Finset.sum_eq_zero ?_
  intro n _
  rw [cyclicConvolutionPow_supported H f hf n k hk, mul_zero]

/-- The finite algebraic logarithmic series stays supported in `H`. -/
theorem truncatedLogSpectrum_supported
    {g : ℕ} [NeZero g] (H : AddSubgroup (ZMod g))
    (M : ℕ) (f : ZMod g → ℂ)
    (hf : ∀ k, k ∉ H → f k = 0) :
    ∀ k, k ∉ H → truncatedLogSpectrum M f k = 0 := by
  intro k hk
  exact finiteConvolutionSeries_supported H _ (M + 1) f hf k hk

/-- Flagship composition: the Phase 1A projected Fourier packet is supported in the
divisor sublattice, hence so is its finite logarithmic convolution series. -/
theorem truncatedLogSpectrum_projected_supported
    {g d : ℕ} [NeZero g] (hd : d ∣ g)
    (M : ℕ) (f : ZMod g → ℂ) :
    ∀ k, k ∉ divisorSublattice g d →
      truncatedLogSpectrum M (positiveDFT (sublatticeProjector d f)) k = 0 := by
  intro k hk
  exact truncatedLogSpectrum_supported (divisorSublattice g d) M _
    (positiveDFT_sublatticeProjector_supported hd f) k hk

end ResidueSlices
