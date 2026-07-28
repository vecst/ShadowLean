/-
Exact finite packet-Fourier identity and its cyclic-variation high-pass bound.
All finite algebra over `ZMod g` — no limits — reusing Mathlib `ZMod.dft` /
`ZMod.stdAddChar` (forward `dft f ℓ = ∑ j χ(−(j·ℓ))·f j`).

Proof routes:
- Target 1: unfold `dft_apply` and `movingPacketMass`, swap the finite sums,
  reindex `r ↦ a q + r`; `χ(−((s−a q)·ℓ)) = χ(a q·ℓ)·χ(−(s·ℓ))` gives the phase
  `χ(a q * ℓ)` with NO minus sign.
- Target 2: unfold `movingPacketMass`/`cyclicDiff`, distribute the difference
  across the sum, normalize `ZMod` addition associativity (`j = a q + r`).
- Target 3: summation by parts — expand `dft_apply`/`cyclicDiff`, reindex the
  `f(j+1)` sum; left factor is `(χ ℓ − 1)`, not its negative.
- Target 4: rewrite by Target 3, `‖·‖` of a sum ≤ sum of `‖·‖`, and `‖χ‖ = 1`.
- Target 5: Target 1 + triangle gives `‖DFT M‖ ≤ ∑_q ‖DFT(b q)‖`; multiply by
  the nonnegative `‖χ ℓ − 1‖` and apply Target 4 termwise.
Keep the product-form bounds (valid at `ℓ = 0`); add no `ℓ ≠ 0` hypothesis.

Honesty: no sorry/admit/unsafe/implemented_by/new axioms; every target an
active declaration; do not weaken hypotheses or specialize the index type; if
a target cannot be closed, omit it and report it explicitly.
-/
import RequestProject.IFFTPreparation

open scoped BigOperators

namespace ResidueSlices

noncomputable def movingPacketMass {g : ℕ} [NeZero g]
    {ι : Type*} [Fintype ι]
    (b : ι → ZMod g → ℂ) (a : ι → ZMod g)
    (r : ZMod g) : ℂ :=
  ∑ q, b q (a q + r)

noncomputable def cyclicDiff {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) (j : ZMod g) : ℂ :=
  f (j + 1) - f j

noncomputable def cyclicVariation {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) : ℝ :=
  ∑ j, ‖cyclicDiff f j‖

/-- Target 1: exact moving-packet DFT identity. -/
theorem dft_movingPacketMass {g : ℕ} [NeZero g]
    {ι : Type*} [Fintype ι]
    (b : ι → ZMod g → ℂ) (a : ι → ZMod g)
    (ℓ : ZMod g) :
    ZMod.dft (movingPacketMass b a) ℓ =
      ∑ q,
        (ZMod.stdAddChar (a q * ℓ) : ℂ) *
          ZMod.dft (b q) ℓ := by
  rw [ZMod.dft_apply]
  unfold movingPacketMass
  simp only [smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  symm
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  symm
  -- reindex with s = a y + x, so x = s - a y
  -- reindex with x = s - a y using Equiv.addRight (-a y)
  conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight (-a y))]
  simp [Equiv.addRight]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have h1 : -((x + -a y) * ℓ) = a y * ℓ + -(x * ℓ) := by ring
  rw [h1]
  simp only [ZMod.stdAddChar_apply]
  have hcomm : -(x * ℓ) = -(ℓ * x) := by ring
  rw [hcomm]
  rw [show ZMod.toCircle (a y * ℓ + -(ℓ * x)) = ZMod.toCircle (a y * ℓ) * ZMod.toCircle (-(ℓ * x)) from by
    simp only [ZMod.toCircle]
    simp only [AddChar.compAddMonoidHom_apply]
    rw [AddMonoidHom.map_add ZMod.toAddCircle]
    exact AddChar.map_add_eq_mul (AddCircle.toCircle_addChar) _ _]
  simp_all [mul_comm, mul_left_comm]

/-- Target 2: exact packet finite-difference identity. -/
theorem movingPacketMass_add_one_sub {g : ℕ} [NeZero g]
    {ι : Type*} [Fintype ι]
    (b : ι → ZMod g → ℂ) (a : ι → ZMod g)
    (r : ZMod g) :
    movingPacketMass b a (r + 1) - movingPacketMass b a r =
      ∑ q, cyclicDiff (b q) (a q + r) := by
  simp [movingPacketMass, cyclicDiff, add_assoc]

/-- Target 3: cyclic Fourier summation by parts. -/
theorem stdAddChar_sub_one_mul_dft {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) (ℓ : ZMod g) :
    ((ZMod.stdAddChar ℓ : ℂ) - 1) * ZMod.dft f ℓ =
      ∑ j,
        (ZMod.stdAddChar (-(j * ℓ)) : ℂ) *
          cyclicDiff f j := by
  unfold cyclicDiff
  rw [ZMod.dft_apply]
  rw [sub_mul, Finset.mul_sum, Finset.mul_sum]
  -- LHS: ∑ j, stdAddChar ℓ * (stdAddChar (-(j * ℓ)) * f j) - ∑ j, stdAddChar (-(j * ℓ)) * f j
  -- Goal: ∑ j, stdAddChar (-(j * ℓ)) * (f (j + 1) - f j)
  -- Reindex the first sum using j ↦ j + 1:
  -- ∑_j χ(ℓ) * χ(-(j*ℓ)) * f(j) = ∑_j χ(-(j*ℓ)) * f(j+1)
  have h1 : ∑ j : ZMod g, (ZMod.stdAddChar ℓ : ℂ) * (ZMod.stdAddChar (-(j * ℓ)) * f j) =
            ∑ j : ZMod g, (ZMod.stdAddChar (-(j * ℓ)) : ℂ) * f (j + 1) := by
    let e : ZMod g ≃ ZMod g := Equiv.addRight (1 : ZMod g)
    rw [← e.sum_comp]
    congr 1
    ext j
    simp only [e, Equiv.coe_addRight]
    ring_nf
    -- Goal: χ(ℓ) * χ(-(j*ℓ) - ℓ) * f(1+j) = f(1+j) * χ(-(j*ℓ))
    have hchar : ZMod.stdAddChar ℓ * ZMod.stdAddChar (-(j * ℓ) - ℓ) = ZMod.stdAddChar (-(j * ℓ)) := by
      simp only [ZMod.stdAddChar_apply]
      rw [← Circle.coe_mul]
      congr 1
      have h1 : (ZMod.toCircle ℓ : Circle) * ZMod.toCircle (-(j * ℓ) - ℓ) =
             ZMod.toCircle (ℓ + (-(j * ℓ) - ℓ)) := by
        simp only [ZMod.toCircle, AddChar.compAddMonoidHom_apply]
        have : AddCircle.toCircle_addChar (ZMod.toAddCircle ℓ) *
               AddCircle.toCircle_addChar (ZMod.toAddCircle (-(j * ℓ) - ℓ)) =
               AddCircle.toCircle_addChar (ZMod.toAddCircle (ℓ + (-(j * ℓ) - ℓ))) := by
          rw [← AddChar.map_add_eq_mul]
          simp
        rw [this]
      rw [h1, show (ℓ : ZMod g) + (-(j * ℓ) - ℓ) = -(j * ℓ) by ring]
    rw [hchar]
    rw [show (1 : ZMod g) + j = j + 1 by ring]
    ring
  simp_rw [smul_eq_mul]
  rw [h1]
  simp only [one_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Target 4: one-block total-variation bound. -/
theorem dft_norm_mul_le_cyclicVariation {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) (ℓ : ZMod g) :
    ‖(ZMod.stdAddChar ℓ : ℂ) - 1‖ * ‖ZMod.dft f ℓ‖ ≤
      cyclicVariation f := by
  rw [← norm_mul]
  rw [stdAddChar_sub_one_mul_dft]
  unfold cyclicVariation
  calc ‖∑ j, (ZMod.stdAddChar (-(j * ℓ)) : ℂ) * cyclicDiff f j‖
      ≤ ∑ j, ‖(ZMod.stdAddChar (-(j * ℓ)) : ℂ) * cyclicDiff f j‖ := norm_sum_le _ _
    _ = ∑ j, ‖ZMod.stdAddChar (-(j * ℓ))‖ * ‖cyclicDiff f j‖ := by simp
    _ = ∑ j, ‖cyclicDiff f j‖ := by simp

/-- Target 5: moving-packet high-pass bound. -/
theorem movingPacket_dft_highpass_bound {g : ℕ} [NeZero g]
    {ι : Type*} [Fintype ι]
    (b : ι → ZMod g → ℂ) (a : ι → ZMod g)
    (ℓ : ZMod g) :
    ‖(ZMod.stdAddChar ℓ : ℂ) - 1‖ *
        ‖ZMod.dft (movingPacketMass b a) ℓ‖ ≤
      ∑ q, cyclicVariation (b q) := by
  rw [dft_movingPacketMass]
  calc ‖ZMod.stdAddChar ℓ - 1‖ * ‖∑ q, ZMod.stdAddChar (a q * ℓ) * ZMod.dft (b q) ℓ‖
      ≤ ‖ZMod.stdAddChar ℓ - 1‖ * ∑ q, ‖ZMod.stdAddChar (a q * ℓ) * ZMod.dft (b q) ℓ‖ := by
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖ZMod.stdAddChar ℓ - 1‖ * ∑ q, ‖ZMod.dft (b q) ℓ‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_mul]
        simp only [ZMod.stdAddChar_apply]
        norm_num [ZMod.toCircle]
    _ ≤ ∑ q, cyclicVariation (b q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro q _
        exact dft_norm_mul_le_cyclicVariation (b q) ℓ

end ResidueSlices
