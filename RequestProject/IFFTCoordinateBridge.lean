/-
Coordinate packet recurrence ↔ spectral flow bridge. Closes the boundary left
open by `IFFTSupportFlow`: the paper's coordinate update
`C_{0,n+1}=C_{0,n}+x·C_{g-1,n}`, `C_{j,n+1}=C_{j,n}+C_{j-1,n}` (x = α^g) is
exactly what `packetSpectrum` diagonalizes to the `1 + α·ζ^k` multiplier, so
the IFFT-evolved packet obeys that coordinate step. Finite cyclic Fourier
algebra only — no convergence/positivity/Poisson/support-equality claims, and
no iterated coordinate-flow theorem (one-step equivalence only).

Key fact behind Target 5: with β = α·χ(k), the wrap term α^g·C(−1) matches the
top contribution C(−1)·β^g because χ(k)^g = stdAddChar(g·k) = stdAddChar 0 = 1,
so α^g = β^g. That is precisely why the paper's x = α^g wrap coefficient is
correct.

Proof routes: T1 finite Fourier inversion of `packetSpectrum` (expand as the
positive transform of `j ↦ C j · α^(j.val)`, invert, cancel α powers via
`α ≠ 0`) — the substantive piece, and a genuine LEFT inverse (not inferred from
the existing right inverse). T2 injectivity from T1. T3-T4 unfold. T5 expand
`packetSpectrum`, shift the non-wrap terms, match the wrap via χ(k)^g = 1
(handle j = 0 explicitly, no g ≥ 2). T6 apply `packetSpectrum` (injective, T2):
left uses `packetSpectrum_evolvedPreparedPacket_succ`, right uses T5.

Certification scope: every target an active declaration; wrap coefficient
exactly `(α:ℂ)^g`; T3-T5 take NO `α ≠ 0`, T1/T2/T6 keep it; `(-1 : ZMod g)` for
the last coordinate (no unsafe Nat subtraction); multiplier sign/orientation
unchanged. If a target cannot close, omit and report it.
-/
import RequestProject.IFFTSupportFlow

open scoped BigOperators

namespace ResidueSlices

/-- The paper's coordinate update: `C_0 ↦ C_0 + α^g·C_{-1}`, and for `j ≠ 0`,
`C_j ↦ C_j + C_{j-1}` (`x = α^g` wrap coefficient). -/
noncomputable def packetCoordinateStep {g : ℕ} [NeZero g]
    (α : ℝ) (C : ZMod g → ℂ) : ZMod g → ℂ :=
  fun j =>
    if j = 0 then
      C 0 + (α : ℂ) ^ g * C (-1)
    else
      C j + C (j - 1)

/-- Target 1: the missing inverse-Fourier direction (left inverse). -/
theorem preparedPacket_packetSpectrum {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) (C : ZMod g → ℂ) :
    preparedPacket α (packetSpectrum α C) = C := by
  funext j
  unfold preparedPacket preparedScaledPacket packetSpectrum
  rw [ZMod.invDFT_apply]
  simp only [smul_eq_mul]
  -- We need to show: α⁻¹^j.val * g⁻¹ * ∑ x, ζ^(x*(-j)) * ∑ i, C i * (α * ζ^x)^i.val = C j
  -- First, interchange the sums
  have sum_comm_eq : ∑ x : ZMod g, ZMod.stdAddChar (x * -j) * ∑ i : ZMod g, C i * ((↑α) * ZMod.stdAddChar x) ^ i.val =
                     ∑ i : ZMod g, C i * ∑ x : ZMod g, ZMod.stdAddChar (x * -j) * ((↑α) * ZMod.stdAddChar x) ^ i.val := by
    rw [show (∑ x : ZMod g, ZMod.stdAddChar (x * -j) * ∑ i : ZMod g, C i * ((↑α) * ZMod.stdAddChar x) ^ i.val) =
             ∑ x : ZMod g, ∑ i : ZMod g, ZMod.stdAddChar (x * -j) * (C i * ((↑α) * ZMod.stdAddChar x) ^ i.val) by
       apply Finset.sum_congr rfl
       intro x _
       rw [← Finset.mul_sum]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [sum_comm_eq]
  -- Now simplify the inner sum: ∑ x, ζ^(x*(-j)) * (α * ζ^x)^i.val
  -- = α^i.val * ∑ x, ζ^(x*(i.val - j))
  -- This equals α^i.val * g when i = j, and 0 otherwise
  have inner_sum_eq : ∀ i : ZMod g, ∑ x : ZMod g, ZMod.stdAddChar (x * -j) * ((↑α) * ZMod.stdAddChar x) ^ i.val =
                      (↑α) ^ i.val * (g : ℂ) * (if i = j then 1 else 0) := by
    intro i
    by_cases hij : i = j
    · -- Case i = j
      subst hij
      simp only [if_true, mul_one]
      -- ∑ x, ζ^(x*(-i)) * (α * ζ^x)^i = α^i * ∑ x, ζ^0 = α^i * g
      have h1 : ∀ x : ZMod g, ZMod.stdAddChar (x * -i) * ((↑α) * ZMod.stdAddChar x) ^ i.val = (↑α) ^ i.val := by
        intro x
        rw [mul_pow]
        have hchar : ZMod.stdAddChar x ^ i.val = ZMod.stdAddChar (i * x) := by
          rw [← AddChar.map_nsmul_eq_pow]
          congr
          rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
        rw [hchar]
        ring_nf
        -- Goal: ZMod.stdAddChar (-(x * i)) * ↑α ^ i.val * ZMod.stdAddChar (x * i) = ↑α ^ i.val
        rw [mul_comm (ZMod.stdAddChar (-(x * i))) _, mul_assoc]
        rw [← AddChar.map_add_eq_mul]
        have : -(x * i) + x * i = 0 := by ring
        rw [this]
        simp [ZMod.stdAddChar]
      simp_rw [h1]
      rw [Finset.sum_const, Finset.card_univ, ZMod.card]
      ring
    · -- Case i ≠ j
      rw [if_neg hij, mul_zero]
      -- ∑ x, ζ^(x*(-j)) * (α * ζ^x)^i = α^i * ∑ x, ζ^(x*(i-j)) = 0 (orthogonality)
      have h1 : ∀ x : ZMod g, ZMod.stdAddChar (x * -j) * ((↑α) * ZMod.stdAddChar x) ^ i.val = (↑α) ^ i.val * ZMod.stdAddChar (x * (i - j)) := by
        intro x
        rw [mul_pow]
        have hchar : ZMod.stdAddChar x ^ i.val = ZMod.stdAddChar (i * x) := by
          rw [← AddChar.map_nsmul_eq_pow]
          congr
          rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
        rw [hchar]
        rw [mul_comm (ZMod.stdAddChar (x * -j)) _, mul_assoc]
        rw [← AddChar.map_add_eq_mul]
        congr 1
        congr 1
        ring
      simp_rw [h1]
      have h2 : ∑ x : ZMod g, ZMod.stdAddChar (x * (i - j)) = 0 := by
        have hi : i - j ≠ 0 := sub_ne_zero.mpr hij
        -- Use AddChar.injective
        have hchi_ne : ZMod.stdAddChar (i - j) ≠ 1 := by
          intro heq
          have h1 : ZMod.stdAddChar (i - j) = ZMod.stdAddChar (0 : ZMod g) := by simp [heq]
          have := ZMod.injective_stdAddChar h1
          exact hi this
        -- stdAddChar (x * (i - j)) = (stdAddChar (i - j)) ^ x.val
        set ζ := ZMod.stdAddChar (i - j) with hζ_def
        have heq : ∀ x : ZMod g, ZMod.stdAddChar (x * (i - j)) = ζ ^ x.val := by
          intro x
          rw [hζ_def]
          rw [← AddChar.map_nsmul_eq_pow]
          congr
          rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
        simp_rw [heq]
        -- ∑ x : ZMod g, ζ ^ x.val = ∑ k in Finset.range g, ζ ^ k = 0
        have hζ_g : ζ ^ g = 1 := by
          rw [hζ_def]
          simp [ZMod.stdAddChar_apply]
          have key : ∀ n : ℕ, (ZMod.toCircle (i - j)) ^ n = ZMod.toCircle (n • (i - j)) := by
            intro n
            rw [← AddChar.map_nsmul_eq_pow ZMod.toCircle]
          rw [← Circle.coe_pow, key g]
          simp
        -- ∑ x : ZMod g, ζ ^ x.val = ∑ k in Finset.range g, ζ ^ k = 0
        have hsum_range : ∑ x : ZMod g, ζ ^ x.val = ∑ i : Fin g, ζ ^ (i : ℕ) := by
          let e : ZMod g ≃ Fin g := {
            toFun := fun x => ⟨x.val, x.val_lt⟩
            invFun := fun i => i.val
            left_inv := fun x => ZMod.natCast_zmod_val x
            right_inv := fun i => Fin.ext <| by simp [Nat.mod_eq_of_lt i.prop]
          }
          rw [← e.sum_comp]; rfl
        rw [hsum_range]
        rw [Finset.sum_fin_eq_sum_range]
        have hfilter : ∀ i ∈ Finset.range g, (if h : i < g then ζ ^ ((⟨i, h⟩ : Fin g) : ℕ) else 0) = ζ ^ i := by
          intro i hi
          simp [Finset.mem_range.mp hi]
        rw [Finset.sum_congr rfl hfilter]
        rw [geom_sum_eq hchi_ne]
        simp [hζ_g]
      rw [show (∑ x : ZMod g, (↑α) ^ i.val * ZMod.stdAddChar (x * (i - j))) =
           (↑α) ^ i.val * ∑ x : ZMod g, ZMod.stdAddChar (x * (i - j)) by rw [Finset.mul_sum]]
      rw [h2, mul_zero]
  -- Now use inner_sum_eq to simplify the sum
  simp_rw [inner_sum_eq]
  rw [Finset.sum_eq_single j]
  · simp only [if_true, mul_one]
    have ha : (α : ℂ) ^ j.val ≠ 0 := pow_ne_zero _ (by simpa using hα)
    have hg : (g : ℂ) ≠ 0 := by simp [NeZero.ne g]
    simp [ha, hg, mul_comm, mul_left_comm]
  · intro i _ hij
    simp [hij]
  · exact fun hj => hj.elim (Finset.mem_univ j)

/-- Target 2: `packetSpectrum` is injective at `α ≠ 0`. -/
theorem packetSpectrum_injective {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) :
    Function.Injective (packetSpectrum (g := g) α) := by
  intro C D h
  rw [← preparedPacket_packetSpectrum hα C,
    ← preparedPacket_packetSpectrum hα D, h]

/-- Target 3: the zero-coordinate recurrence. -/
theorem packetCoordinateStep_zero {g : ℕ} [NeZero g]
    (α : ℝ) (C : ZMod g → ℂ) :
    packetCoordinateStep α C 0 =
      C 0 + (α : ℂ) ^ g * C (-1) := by
  simp [packetCoordinateStep]

/-- Target 4: every nonzero-coordinate recurrence. -/
theorem packetCoordinateStep_ne_zero {g : ℕ} [NeZero g]
    (α : ℝ) (C : ZMod g → ℂ) {j : ZMod g} (hj : j ≠ 0) :
    packetCoordinateStep α C j = C j + C (j - 1) := by
  simp [packetCoordinateStep, hj]

/-- Target 5: Fourier diagonalization of the actual coordinate update. -/
theorem packetSpectrum_packetCoordinateStep {g : ℕ} [NeZero g]
    (α : ℝ) (C : ZMod g → ℂ) (k : ZMod g) :
    packetSpectrum α (packetCoordinateStep α C) k =
      packetSpectrum α C k *
        (1 + (α : ℂ) * ZMod.stdAddChar k) := by
  unfold packetSpectrum packetCoordinateStep
  set χ := ZMod.stdAddChar k with hχ
  set x := (α : ℂ) * χ with hx
  -- Goal: ∑ j, (if j = 0 then C 0 + α^g * C(-1) else C j + C(j-1)) * x^j.val = (∑ j, C j * x^j.val) * (1 + x)
  have χ_pow_g : χ ^ g = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  have hx_pow_g : x ^ g = (α : ℂ) ^ g := by
    rw [hx, mul_pow, χ_pow_g, mul_one]
  -- Split sum at j = 0
  have hsplit : ∑ j : ZMod g, (if j = 0 then C 0 + (α : ℂ) ^ g * C (-1) else C j + C (j - 1)) * x ^ j.val =
    (C 0 + (α : ℂ) ^ g * C (-1)) +
    ∑ j ∈ Finset.univ.erase 0, (C j + C (j - 1)) * x ^ j.val := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod g))]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_erase] at hj
      simp [hj.1]
  rw [hsplit]
  -- Goal: C 0 + α^g * C(-1) + ∑ j ≠ 0, (C j + C(j-1)) * x^j = (∑ j, C j * x^j) * (1 + x)
  -- RHS = (∑ j, C j * x^j) + x * (∑ j, C j * x^j)
  have hrhs : (∑ j : ZMod g, C j * x ^ j.val) * (1 + x) =
    ∑ j : ZMod g, C j * x ^ j.val + ∑ j : ZMod g, C j * x ^ (j.val + 1) := by
    rw [mul_add, mul_one]
    congr 1
    simp only [pow_succ]
    conv_lhs => rw [mul_comm]
    rw [Finset.mul_sum _ _ _]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hrhs]
  -- Goal: C 0 + α^g * C(-1) + ∑ j ≠ 0, (C j + C(j-1)) * x^j = ∑ j, C j * x^j + ∑ j, C j * x^(j+1)
  -- Expand LHS sum
  have hlhs_sum : ∑ j ∈ Finset.univ.erase 0, (C j + C (j - 1)) * x ^ j.val =
    ∑ j ∈ Finset.univ.erase 0, C j * x ^ j.val + ∑ j ∈ Finset.univ.erase 0, C (j - 1) * x ^ j.val := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlhs_sum]
  -- Goal: C 0 + α^g * C(-1) + (∑ j≠0, C j * x^j + ∑ j≠0, C(j-1) * x^j) = ∑ j, C j * x^j + ∑ j, C j * x^(j+1)
  -- First, reorganize: C 0 + ∑ j≠0, C j * x^j = ∑ j, C j * x^j
  have hsum_split : C 0 + ∑ j ∈ Finset.univ.erase 0, C j * x ^ j.val = ∑ j : ZMod g, C j * x ^ j.val := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod g))]
    simp
  -- Combine C 0 + ∑ x≠0, C x * x^x.val = ∑ x, C x * x^x.val
  have lhs1 : C 0 + ∑ x_1 ∈ Finset.univ.erase 0, C x_1 * x ^ x_1.val = ∑ x_1 : ZMod g, C x_1 * x ^ x_1.val := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod g))]
    simp
  rw [show C 0 + (α : ℂ) ^ g * C (-1) + (∑ j ∈ Finset.univ.erase 0, C j * x ^ j.val + ∑ j ∈ Finset.univ.erase 0, C (j - 1) * x ^ j.val) =
      (C 0 + ∑ j ∈ Finset.univ.erase 0, C j * x ^ j.val) +
      ((α : ℂ) ^ g * C (-1) + ∑ j ∈ Finset.univ.erase 0, C (j - 1) * x ^ j.val) by ring]
  rw [lhs1]
  -- Need: α^g * C(-1) + ∑ j≠0, C(j-1) * x^j = ∑ j, C j * x^(j+1)
  -- Reindex: let i = j - 1, so j = i + 1. When j ≠ 0, i ≠ -1.
  have hreindex : ∑ j ∈ Finset.univ.erase 0, C (j - 1) * x ^ j.val =
    ∑ i ∈ Finset.univ.erase (-1 : ZMod g), C i * x ^ (i + 1).val := by
    symm
    refine Finset.sum_bij (fun i hi => i + 1) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_erase] at ha ⊢
      simp_all [add_eq_zero_iff_eq_neg]
    · intro a ha b hb h
      simp at h
      exact h
    · intro b hb
      simp only [Finset.mem_erase] at hb ⊢
      use b - 1
      simp [hb.1]
    · intro a ha
      simp
  rw [hreindex]
  -- Need: α^g * C(-1) + ∑ i ≠ -1, C i * x ^ ((i+1).val) = ∑ j, C j * x ^ (j.val + 1)
  -- Split RHS at j = -1
  have hrhs_split : ∑ j : ZMod g, C j * x ^ (j.val + 1) =
    C (-1) * x ^ ((-1 : ZMod g).val + 1) + ∑ j ∈ Finset.univ.erase (-1 : ZMod g), C j * x ^ (j.val + 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (-1 : ZMod g))]
    ring
  rw [hrhs_split]
  -- Cancel matching sums
  have heq_sums : ∑ i ∈ Finset.univ.erase (-1 : ZMod g), C i * x ^ (i + 1).val =
    ∑ j ∈ Finset.univ.erase (-1 : ZMod g), C j * x ^ (j.val + 1) := by
    by_cases hg1 : g = 1
    · subst hg1; rfl
    · have hg2 : 1 < g := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne g)) (Ne.symm hg1)
      have : Fact (1 < g) := ⟨hg2⟩
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_erase] at hj
      congr 1
      have hj2 : j.val ≠ g - 1 := by
        intro h
        apply hj.1
        rw [← ZMod.natCast_zmod_val j, h]
        rw [Nat.cast_sub (Nat.one_le_of_lt hg2)]
        rw [sub_eq_iff_eq_add]
        simp
      have hj3 : j.val < g := ZMod.val_lt j
      have hj4 : j.val + ZMod.val (1 : ZMod g) < g := by simp [ZMod.val_one]; omega
      rw [ZMod.val_add_of_lt hj4, ZMod.val_one]
  rw [heq_sums]
  -- Now just need: α^g * C(-1) = C(-1) * x^((-1).val + 1)
  have hwrap : x ^ ((-1 : ZMod g).val + 1) = x ^ g := by
    have hg : g ≠ 0 := NeZero.ne g
    have h1 : (-1 : ZMod g).val = g - 1 := by
      cases g with
      | zero => contradiction
      | succ n => simp
    rw [h1]
    rw [show g - 1 + 1 = g from Nat.sub_add_cancel (Nat.pos_of_ne_zero hg)]
  rw [hwrap, hx_pow_g]
  ring

/-- Target 6: the IFFT-evolved packet obeys the paper's coordinate step. -/
theorem evolvedPreparedPacket_succ_eq_packetCoordinateStep {g : ℕ} [NeZero g]
    {α : ℝ} (hα : α ≠ 0) (V : ZMod g → ℂ) (n : ℕ) :
    evolvedPreparedPacket α V (n + 1) =
      packetCoordinateStep α (evolvedPreparedPacket α V n) := by
  apply packetSpectrum_injective hα
  funext k
  rw [packetSpectrum_evolvedPreparedPacket_succ hα V n k,
    packetSpectrum_packetCoordinateStep]

end ResidueSlices
