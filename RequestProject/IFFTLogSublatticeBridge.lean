import RequestProject.IFFTSublatticeConvolution

open scoped BigOperators

namespace ResidueSlices

/-- The normalized positive-sign DFT used by the paper's Fourier coefficients. -/
noncomputable def normalizedPositiveDFT {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) : ZMod g → ℂ :=
  fun k => (g : ℂ)⁻¹ * positiveDFT f k

theorem positiveDFT_injective {g : ℕ} [NeZero g] :
    Function.Injective (positiveDFT : (ZMod g → ℂ) → ZMod g → ℂ) := by
  intro f h hfh
  apply ZMod.dft.injective
  funext k
  have hk := congrFun hfh (-k)
  simpa only [positiveDFT, ZMod.dft_apply, neg_neg, mul_neg, smul_eq_mul] using hk

theorem sublatticeProjector_eq_self_of_supported
    {g d : ℕ} [NeZero g] (hd : d ∣ g) (f : ZMod g → ℂ)
    (hf : ∀ k, k ∉ divisorSublattice g d → positiveDFT f k = 0) :
    sublatticeProjector d f = f := by
  apply positiveDFT_injective
  funext k
  by_cases hk : k ∈ divisorSublattice g d
  · exact positiveDFT_sublatticeProjector_of_mem hd f hk
  · rw [positiveDFT_sublatticeProjector_of_not_mem hd f hk, hf k hk]

theorem sublatticeProjector_pointwise_map
    {g d : ℕ} [NeZero g] (hd : d ∣ g)
    (F : ℂ → ℂ) (f : ZMod g → ℂ) :
    sublatticeProjector d (fun r => F (sublatticeProjector d f r)) =
      fun r => F (sublatticeProjector d f r) := by
  have hm0 : ((g / d : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (divisor_quotient_pos hd).ne'
  have hshift : ∀ (r : ZMod g) (t : ℕ),
      sublatticeProjector d f (r + ((t * d : ℕ) : ZMod g)) =
        sublatticeProjector d f r := by
    intro r t
    rw [sublatticeProjector_apply, sublatticeProjector_apply,
      sublatticeProjector_sum_shift hd f r t]
  funext r
  rw [sublatticeProjector_apply]
  rw [Finset.sum_congr rfl fun ell (_ : ell ∈ Finset.univ) =>
    congrArg F (hshift r ell.val)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem positiveDFT_pointwise_map_supported_of_supported
    {g d : ℕ} [NeZero g] (hd : d ∣ g)
    (F : ℂ → ℂ) (f : ZMod g → ℂ)
    (hf : ∀ k, k ∉ divisorSublattice g d → positiveDFT f k = 0) :
    ∀ k, k ∉ divisorSublattice g d →
      positiveDFT (fun r => F (f r)) k = 0 := by
  intro k hk
  have hfix := sublatticeProjector_eq_self_of_supported hd f hf
  have hmap := sublatticeProjector_pointwise_map hd F f
  rw [hfix] at hmap
  rw [← hmap]
  exact positiveDFT_sublatticeProjector_of_not_mem hd _ hk

theorem positiveDFT_log_one_add_supported_of_supported
    {g d : ℕ} [NeZero g] (hd : d ∣ g)
    (e : ZMod g → ℂ)
    (he : ∀ k, k ∉ divisorSublattice g d → positiveDFT e k = 0) :
    ∀ k, k ∉ divisorSublattice g d →
      positiveDFT (fun r => Complex.log (1 + e r)) k = 0 := by
  exact positiveDFT_pointwise_map_supported_of_supported hd
    (fun z => Complex.log (1 + z)) e he

/-- The paper's filter polynomial evaluated at the negative Fourier character. -/
noncomputable def packetFilterValue {g : ℕ} [NeZero g]
    (w : ZMod g → ℂ) (k : ZMod g) : ℂ :=
  ∑ j : ZMod g, w j * ZMod.stdAddChar (-(k * j))

theorem inverse_normalizedPositiveDFT
    {g : ℕ} [NeZero g] (f : ZMod g → ℂ) (j : ZMod g) :
    f j = ∑ k : ZMod g,
      normalizedPositiveDFT f k * ZMod.stdAddChar (-(k * j)) := by
  have hinv : preparedScaledPacket (positiveDFT f) = f :=
    positiveDFT_injective (positiveDFT_preparedScaledPacket (positiveDFT f))
  rw [← congrFun hinv j, preparedScaledPacket_formula]
  unfold normalizedPositiveDFT
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem weighted_inverse_fourier_sum
    {g : ℕ} [NeZero g] (w b : ZMod g → ℂ) :
    (∑ j : ZMod g,
      w j * (∑ k : ZMod g, b k * ZMod.stdAddChar (-(k * j)))) =
      ∑ k : ZMod g, b k * packetFilterValue w k := by
  simp only [packetFilterValue, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by
    exact Finset.sum_congr rfl fun j _ => by ring

theorem logarithmic_estimator_annihilated
    {g d : ℕ} [NeZero g] (hd : d ∣ g)
    (e w : ZMod g → ℂ)
    (he : ∀ k, k ∉ divisorSublattice g d → positiveDFT e k = 0)
    (hw : ∀ k, k ∈ divisorSublattice g d → packetFilterValue w k = 0) :
    ∑ j : ZMod g, w j * Complex.log (1 + e j) = 0 := by
  let L : ZMod g → ℂ := fun j => Complex.log (1 + e j)
  have hL : ∀ k, k ∉ divisorSublattice g d → positiveDFT L k = 0 :=
    positiveDFT_log_one_add_supported_of_supported hd e he
  calc
    (∑ j : ZMod g, w j * Complex.log (1 + e j)) =
        ∑ j : ZMod g, w j *
          (∑ k : ZMod g,
            normalizedPositiveDFT L k * ZMod.stdAddChar (-(k * j))) := by
          apply Finset.sum_congr rfl
          intro j _
          change w j * L j = _
          rw [inverse_normalizedPositiveDFT L j]
    _ = ∑ k : ZMod g, normalizedPositiveDFT L k * packetFilterValue w k :=
      weighted_inverse_fourier_sum w (normalizedPositiveDFT L)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : k ∈ divisorSublattice g d
      · rw [hw k hk, mul_zero]
      · unfold normalizedPositiveDFT
        rw [hL k hk, mul_zero, zero_mul]

end ResidueSlices
