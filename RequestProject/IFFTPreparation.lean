/-
Inverse-Fourier packet preparation and its real/positive guardrails
(`Research/shadow_packetization_companions.tex`, the inverse-Fourier
preparation paragraph after the Sublattice-projector proposition).

The point is EXACT spectral reconstruction at finite `g` — no `g → ∞`.
Reuse Mathlib's `ZMod.dft` (a `ℂ`-linear equiv, so `dft.symm` is the inverse
DFT); `stdAddChar j = exp(2πi j/g)`; the forward `dft` uses the `−(j*k)` sign,
so `positiveDFT` (the `+(j*k)` sign) is its inversion partner.

Proof routes:
- Target 1: unfold `dft.symm` (its explicit formula is `g⁻¹·∑ V k·χ(−k·j)`);
  `preparedScaledPacket V j = dft.symm V (-j)`, so the sign lands on `+k·j`
  becoming `−(k·(−j))` — reconcile with the Mathlib `dft_symm`/inversion lemma.
- Targets 2–3: Fourier inversion (`dft.symm`/`dft` round-trip); in Target 3
  the `α^{-j}` from `preparedPacket` cancels the `α^j` in `packetSpectrum`
  (needs `α ≠ 0`), reducing to Target 2's `positiveDFT ∘ preparedScaledPacket`.
- Target 4: immediate from Target 3 — `packetSpectrum α (preparedPacket α V) k
  = V k = 0` for `k ∉ S`.
- Target 5: `star (preparedScaledPacket V j) = preparedScaledPacket V (-... )`;
  the hypothesis `V(-k) = star (V k)` makes the coefficient sum self-conjugate,
  and `α > 0` keeps `(α⁻¹)^j.val` real. Do NOT weaken to arbitrary real V.
- Target 6: the `k = 0` term of `g⁻¹·∑ V k·χ(−k·j)` is `g⁻¹·(V 0).re` (real by
  conj symmetry at `k=0`); the rest have real part `≥ −g⁻¹·∑_{k≠0}‖V k‖`, so
  `Re(preparedScaledPacket V j) ≥ g⁻¹·((V 0).re − ∑_{k≠0}‖V k‖) > 0`, times
  `(α⁻¹)^j.val > 0`. Strict positivity needs exactly the dominance hypothesis;
  do NOT weaken to `≥ 0` or to `(V 0).re > 0` alone.

Honesty: no sorry/admit/implemented_by/unsafe/new axioms; every target an
active declaration (not commented out); keep `α ≠ 0` (Targets 3–4) and
`α > 0` (Targets 5–6); if a target cannot be closed, leave it out and report
it explicitly.
-/
import RequestProject.GeneralResidueConvergence
import Mathlib.Analysis.Fourier.ZMod

open scoped BigOperators

namespace ResidueSlices

noncomputable def positiveDFT {g : ℕ} [NeZero g]
    (f : ZMod g → ℂ) : ZMod g → ℂ :=
  fun k => ∑ j : ZMod g, ZMod.stdAddChar (j * k) * f j

noncomputable def preparedScaledPacket {g : ℕ} [NeZero g]
    (V : ZMod g → ℂ) : ZMod g → ℂ :=
  fun j => ZMod.dft.symm V (-j)

noncomputable def preparedPacket {g : ℕ} [NeZero g]
    (α : ℝ) (V : ZMod g → ℂ) : ZMod g → ℂ :=
  fun j => ((α : ℂ)⁻¹) ^ j.val * preparedScaledPacket V j

noncomputable def packetSpectrum {g : ℕ} [NeZero g]
    (α : ℝ) (C : ZMod g → ℂ) : ZMod g → ℂ :=
  fun k =>
    ∑ j : ZMod g,
      C j * ((α : ℂ) * ZMod.stdAddChar k) ^ j.val

theorem preparedScaledPacket_formula {g : ℕ} [NeZero g]
    (V : ZMod g → ℂ) (j : ZMod g) :
    preparedScaledPacket V j =
      (g : ℂ)⁻¹ *
        ∑ k : ZMod g, V k * ZMod.stdAddChar (-(k * j)) := by
  unfold preparedScaledPacket
  rw [ZMod.invDFT_apply]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm k j]
  ring_nf

theorem positiveDFT_preparedScaledPacket {g : ℕ} [NeZero g]
    (V : ZMod g → ℂ) :
    positiveDFT (preparedScaledPacket V) = V := by
  ext k
  change (∑ j : ZMod g, ZMod.stdAddChar (j * k) * ZMod.dft.symm V (-j)) = V k
  rw [show (∑ j : ZMod g, ZMod.stdAddChar (j * k) * ZMod.dft.symm V (-j)) =
      ZMod.dft (fun j => ZMod.dft.symm V (-j)) (-k) by
        rw [ZMod.dft_apply]
        simp only [mul_neg, neg_neg, smul_eq_mul]]
  rw [show ZMod.dft (fun j => ZMod.dft.symm V (-j)) (-k) =
      ZMod.dft (ZMod.dft.symm V) k by
        rw [ZMod.dft_apply, ZMod.dft_apply]
        simpa only [neg_neg] using
          (Fintype.sum_equiv (Equiv.neg (ZMod g))
            (fun j : ZMod g => ZMod.stdAddChar (- (j * -k)) • ZMod.dft.symm V (-j))
            (fun j : ZMod g => ZMod.stdAddChar (- (j * k)) • ZMod.dft.symm V j)
            (fun j => by simp [mul_comm]))]
  exact congrFun (ZMod.dft.apply_symm_apply V) k

theorem packetSpectrum_preparedPacket {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) (V : ZMod g → ℂ) :
    packetSpectrum α (preparedPacket α V) = V := by
  calc
    packetSpectrum α (preparedPacket α V) = positiveDFT (preparedScaledPacket V) := by
      funext k
      unfold packetSpectrum preparedPacket positiveDFT
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      have hchar : ZMod.stdAddChar k ^ j.val = ZMod.stdAddChar (j * k) := by
        rw [← AddChar.map_nsmul_eq_pow]
        congr
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
      rw [hchar]
      have hc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
      have hp : ((α : ℂ)⁻¹) ^ j.val * (α : ℂ) ^ j.val = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hc, one_pow]
      calc
        (α : ℂ)⁻¹ ^ j.val * preparedScaledPacket V j *
            ((α : ℂ) ^ j.val * ZMod.stdAddChar (j * k)) =
          (((α : ℂ)⁻¹ ^ j.val * (α : ℂ) ^ j.val) *
            preparedScaledPacket V j * ZMod.stdAddChar (j * k)) := by ring
        _ = ZMod.stdAddChar (j * k) * preparedScaledPacket V j := by rw [hp]; ring
    _ = V := positiveDFT_preparedScaledPacket V

theorem preparedPacket_no_spectral_leakage {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) (V : ZMod g → ℂ)
    (S : Set (ZMod g))
    (hV : ∀ k, k ∉ S → V k = 0) :
    ∀ k, k ∉ S → packetSpectrum α (preparedPacket α V) k = 0 := by
  intro k hk
  rw [packetSpectrum_preparedPacket hα V]
  exact hV k hk

theorem preparedPacket_conj_eq_self {g : ℕ} [NeZero g]
    {α : ℝ} (hα : 0 < α) (V : ZMod g → ℂ)
    (hV : ∀ k, V (-k) = star (V k)) :
    ∀ j, star (preparedPacket α V j) = preparedPacket α V j := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hscaled : ∀ j, star (preparedScaledPacket V j) = preparedScaledPacket V j := by
    intro j
    simp only [preparedScaledPacket_formula]
    have hchar (x : ZMod g) :
        star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
      simp only [Complex.star_def, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj,
        ← Circle.coe_inv, AddChar.map_neg_eq_inv]
    simp only [star_mul', star_inv₀, star_sum, hchar]
    rw [show star (g : ℂ) = (g : ℂ) by simp]
    congr 1
    rw [show (∑ x : ZMod g, star (V x) * ZMod.stdAddChar (-(-(x * j)))) =
        ∑ x : ZMod g, V (-x) * ZMod.stdAddChar (x * j) by
          apply Finset.sum_congr rfl
          intro x _
          rw [hV]
          simp only [neg_neg]]
    simpa only [neg_mul, neg_neg] using
      (Fintype.sum_equiv (Equiv.neg (ZMod g))
        (fun x : ZMod g => V (-x) * ZMod.stdAddChar (x * j))
        (fun x : ZMod g => V x * ZMod.stdAddChar (-(x * j)))
        (fun x => by simp))
  intro j
  unfold preparedPacket
  rw [star_mul', hscaled]
  have _ : (α : ℂ) ≠ 0 := by exact_mod_cast hα0
  congr 1
  simp


theorem preparedPacket_pos_of_dominant_zero {g : ℕ} [NeZero g]
    {α : ℝ} (hα : 0 < α) (V : ZMod g → ℂ)
    (hV : ∀ k, V (-k) = star (V k))
    (hdom :
      ∑ k ∈ (Finset.univ.erase (0 : ZMod g)), ‖V k‖ < (V 0).re) :
    ∀ j, 0 < (preparedPacket α V j).re := by
  have hV0 : V 0 = star (V 0) := by simpa using hV 0
  clear hV0
  intro j
  unfold preparedPacket
  rw [preparedScaledPacket_formula]
  -- Goal: 0 < ((α⁻¹)^j.val * (g⁻¹ * ∑ x, V x * ZMod.stdAddChar (-(j * x)))).re
  -- Factor out: ((α⁻¹)^j.val * g⁻¹) * (∑ x, V x * ZMod.stdAddChar (-(j * x))).re
  have hfactor : ((α : ℂ)⁻¹ ^ j.val * ((g : ℂ)⁻¹ * ∑ k, V k * ZMod.stdAddChar (-(k * j)))).re =
    ((α : ℝ)⁻¹ ^ j.val * (g : ℝ)⁻¹) * (∑ k, V k * ZMod.stdAddChar (-(k * j))).re := by
    have h1 : ((α : ℂ)⁻¹ ^ j.val) = (((α : ℝ)⁻¹ ^ j.val : ℝ) : ℂ) := by norm_cast
    have h2 : ((g : ℂ)⁻¹) = (((g : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [h1, h2]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hfactor]
  -- Need to show: 0 < ((α : ℝ)⁻¹ ^ j.val * (g : ℝ)⁻¹) * (∑ x, ...).re
  apply mul_pos _ _
  · -- (α⁻¹)^j.val * g⁻¹ > 0
    apply mul_pos (pow_pos (inv_pos.mpr hα) j.val) (inv_pos.mpr (by exact_mod_cast NeZero.pos g : (0 : ℝ) < g))
  · -- (∑ k, V k * ZMod.stdAddChar (-(k * j))).re > 0
    -- Split sum into k=0 and k≠0
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod g))]
    -- ZMod.stdAddChar 0 = 1
    have hchar0 : ZMod.stdAddChar (-(0 * j)) = 1 := by simp
    rw [hchar0, mul_one]
    rw [Complex.add_re]
    -- Bound: Re(∑ x ∈ ..., ...) ≥ -∑ x ∈ ..., ‖V x‖
    have hbound : (∑ x ∈ Finset.univ.erase 0, V x * ZMod.stdAddChar (-(x * j))).re ≥
        -∑ x ∈ Finset.univ.erase 0, ‖V x‖ := by
      have h1 : (∑ x ∈ Finset.univ.erase 0, V x * ZMod.stdAddChar (-(x * j))).re ≥
          -‖∑ x ∈ Finset.univ.erase 0, V x * ZMod.stdAddChar (-(x * j))‖ := by
        have := Complex.abs_re_le_norm (∑ x ∈ Finset.univ.erase 0, V x * ZMod.stdAddChar (-(x * j)))
        linarith [abs_le.mp this]
      have h2 : ‖∑ x ∈ Finset.univ.erase 0, V x * ZMod.stdAddChar (-(x * j))‖ ≤
          ∑ x ∈ Finset.univ.erase 0, ‖V x * ZMod.stdAddChar (-(x * j))‖ :=
        norm_sum_le _ _
      have h3 : ∑ x ∈ Finset.univ.erase 0, ‖V x * ZMod.stdAddChar (-(x * j))‖ =
          ∑ x ∈ Finset.univ.erase 0, ‖V x‖ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Complex.norm_mul]
        simp
      linarith
    linarith

end ResidueSlices
