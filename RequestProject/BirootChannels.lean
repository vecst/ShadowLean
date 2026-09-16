/-
Channel dominance for general residue-packet rows (linear DAGs), its sharpness, and
the generalized binomial biroot conjecture.

Context. `ResidueSlices.slice g r N x` compresses one residue class of the Pascal row
`(1+X)^N`. Isaac Wolford, "Combinatorial and Gaussian Foundations of Rational Nth Root
Approximations" (arXiv:2508.14095, 2025), states the same construction as the
"binomial biroot" `β_m^n(x,c)`, proves only `n = 2`, and conjectures convergence to
`x^(1/n)` for every `n` (his Conjecture 3.4); he also proposes, without a stated
mechanism, that rows of arbitrary "linearly constructed DAGs" work. This file makes
both precise:

* a linear DAG level is exactly the row of `B * W^m` (basin `B`, weight polynomial
  `W`), so its compressed slices are `polySlice (B * W^m) g r x`;
* the slice ratio converges to the reciprocal power of the DOMINANT roots-of-unity
  channel of `W` (Targets 5-7): convergence to the true root holds exactly when the
  real channel `W(t)` dominates, at geometric rate `max_{a≠0} |W(tω^a)| / |W(t)|`;
* for nonnegative weights, dominance is a phase-separation condition on the exponents
  (Targets 8-10), and it genuinely fails for skip rows `W = 1 + X^2` at `g = 2`
  (Targets 11-12) and for mixed signs, which converge to the negative root (Target 13);
* Wolford's `β_m^n(x,c)` equals `c * slice n 0 m (x/c^n) / slice n 1 m (x/c^n)`
  (Target 14), so his Conjecture 3.4 follows from `tendsto_slice_ratio_rpow`
  (Target 15).

These statements were first checked numerically (exact rationals / 500-digit
arithmetic) in `numerics/biroot_channels.py` and against the biroot formula on 1278
cases; the proofs below discharge them in Lean.

Proof routes:
- T1 polySlice_one_add_X_pow: `natDegree ((1+X)^N) = N` over `ℝ`; coefficients are
  `N.choose j` (e.g. `Polynomial.coeff_one_add_X_pow` / `coeff_X_add_one_pow`, after
  `add_comm`); unfold `polySlice`, `slice`, `Finset.sum_congr`.
- T2 polySlice_eq_sum_of_natDegree_lt: split `range D` at `natDegree + 1`; the extra
  coefficients vanish (`Polynomial.coeff_eq_zero_of_natDegree_lt`).
- T3 dagNode_eq_coeff: induction on `m` generalizing `i`. Base `pow_zero, mul_one`.
  Step: `pow_succ`, `← mul_assoc`, expand `dagWeightPoly` as a finite sum of
  `C w_j * X^(j*s)`, `Finset.mul_sum`, `Polynomial.finset_sum_coeff`,
  `Polynomial.coeff_mul_C`, `Polynomial.coeff_mul_X_pow'` (which produces exactly the
  `if j*s ≤ i then coeff (i - j*s) else 0` shape).
- T4 polySlice_roots_of_unity_filter: write `aeval z P = ∑_{j ≤ natDegree} coeff j * z^j`
  (`Polynomial.aeval_eq_sum_range`), swap sums, apply the repo's
  `primitive_root_power_sum` to `∑_a ω^(a*(g-k+j))` (it is `g` iff `j % g = k`, as in
  `roots_of_unity_filter`), and use `j = k + g*(j/g)` when `j % g = k`.
- T5 tendsto_polySlice_ratio_of_dominant_channel: follow the proof of
  `tendsto_general_slice_ratio_of_dominance`, replacing `(1 + tω^a)^N` by
  `aeval(tω^a) B * aeval(tω^a) W ^ m` (`map_mul`, `map_pow`). Divide T4 (for `k` and
  for `0`) by `g * aeval(tω^a₀) W ^ m`; every channel `a ≠ a₀` tends to `0` because
  `‖W(tω^a)‖ / ‖W(tω^a₀)‖ < 1`; the `a₀` channel is the constant `ω^(a₀(g-k)) * B(tω^a₀)`
  (resp. `B(tω^a₀)`, using `ω^(a₀ g) = 1`). The limit quotient is
  `ω^(a₀(g-k)) / t^k = ((t ω^a₀)^k)⁻¹` (`hω.pow_eq_one`). `hW` is needed for `g = 1`.
- T6 tendsto_polySlice_ratio_of_dominance: T5 with `a₀ = 0`, `aeval (t:ℂ) P = (eval t P : ℂ)`
  (`Polynomial.aeval_algebraMap_apply` / `Polynomial.eval₂_at_ofReal`-style lemmas), then
  take real parts or use `Complex.ofReal` injectivity of the limit (as in
  `tendsto_general_slice_ratio_of_dominance`, which ends with `Complex.continuous_re`).
- T7 polySlice_ratio_geometric_rate: follow `general_slice_ratio_spectral_rate` /
  `packet_principal_deviation`: bound each subordinate channel by `ρ^m` times a constant,
  get the denominator above half its principal part eventually, and combine.
- T8 nonneg_weights_channel_lt: `aeval (tω^a) W = ∑ c_j t^j ω^(aj)` with all `c_j t^j ≥ 0`;
  strict triangle inequality for two nonzero terms with distinct unit phases
  (`‖ω‖ = 1` from `hω.norm'_eq_one hg.ne'`; e.g. `not_sameRay_iff_norm_add_lt` or
  `Complex.norm_add_eq_iff`-type lemmas), and `∑ c_j t^j = eval t W`.
- T9 nonneg_weights_channel_eq: all nonzero terms share the phase `u = ω^(a i₀)`, so the
  sum is `u * eval t W` with `‖u‖ = 1`; the zero polynomial case is trivial.
- T10 nonneg_weights_dominance_iff: `→` by contraposition using T9 (equality contradicts
  `<`); `←` by T8.
- T11 skipRow_slices: `(1+X)(1+X^2)^m = ∑ C(m,i) X^(2i) + ∑ C(m,i) X^(2i+1)`
  (`add_pow` in `X^2`); even indices `2i` compress to `x^i`, odd indices `2i+1` to `x^i`;
  both slices are `∑ C(m,i) x^i = (1+x)^m`. `natDegree = 2m+1` (or use T2 with
  `D = 2m+2`).
- T12 skipRow_ratio_not_tendsto: by T11 the sequence is constantly `1` (`(1+4)^m ≠ 0`),
  so its limit is `1 ≠ 1/2` (`tendsto_nhds_unique`).
- T13 mixedSign_ratio_tendsto_neg: T5 over `ℂ` with `g = 2`, `ω = -1`
  (`IsPrimitiveRoot.neg_one` / `Complex` char ≠ 2), `a₀ = 1`, `B = 1`: channels
  `W(t) = 1 - t + t^2`, `W(-t) = 1 + t + t^2`, and `0 < 1 - t + t^2 < 1 + t + t^2` for
  `t > 0`; the complex limit `((t * (-1))^1)⁻¹ = -t⁻¹` is real, transfer to `ℝ`.
- T14 binomialBiroot_eq_slice_ratio: with `y = x / c^n`,
  numerator `= c^m * slice n 0 m y` (terms `k` with `n*k ≤ m`; `choose` vanishes otherwise
  and `(m + n - 1)/n` covers every `k ≤ m/n`), denominator `= c^(m-1) * slice n 1 m y`
  (index `j = n*k + 1`, `j / n = k` because `1 < n`). Case `m = 0`: both sides are `0`
  (empty denominator, `slice n 1 0 = 0`). Uses `2 ≤ n` (false for `n = 1`).
- T15 tendsto_binomialBiroot: T14, then `tendsto_slice_ratio_rpow` with `k = 1` at
  `y = x / c^n > 0` gives `slice n 1 m y / slice n 0 m y → y^(-1/n)`; invert
  (`Filter.Tendsto.inv₀`, limit ≠ 0) and multiply by `c`; finally
  `c * (y^(-1/n))⁻¹ = x^(1/n)` (`Real.div_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`).

Every target's transitive axioms stay within `{propext, Classical.choice, Quot.sound}`
(recorded in `audit/AxiomAudit.lean`). Deferred (not in this file): the Gaussian
variant, which needs Poisson summation plus edge-truncation estimates.
-/
import RequestProject.RpowCorollaries

open scoped BigOperators

namespace ResidueSlices

/-- Compressed residue slice of an arbitrary coefficient row `P`:
`∑_{j ≡ r (mod g)} P_j · x^⌊j/g⌋`. For `P = (1+X)^N` this is `slice g r N x` (T1). -/
noncomputable def polySlice (P : Polynomial ℝ) (g r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    if j % g = r then P.coeff j * x ^ (j / g) else 0

/-- Weight polynomial of a linear DAG with weights `w` (arity `w.length`) and step `s`:
`W(z) = ∑_j w_j z^(j*s)`. -/
noncomputable def dagWeightPoly (w : List ℝ) (s : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range w.length, Polynomial.C (w.getD j 0) * Polynomial.X ^ (j * s)

/-- Node values of the linear DAG: level `0` is the basin, and node `i` of level `m+1`
is `∑_j w_j · (node i - j*s of level m)`, with parents outside the row equal to zero. -/
noncomputable def dagNode (basin : Polynomial ℝ) (w : List ℝ) (s : ℕ) : ℕ → ℕ → ℝ
  | 0, i => basin.coeff i
  | m + 1, i => ∑ j ∈ Finset.range w.length,
      if j * s ≤ i then w.getD j 0 * dagNode basin w s m (i - j * s) else 0

/-- Wolford's binomial biroot `β_m^n(x, c)` (arXiv:2508.14095), with
`⌈m/n⌉ = (m + n - 1) / n`: numerator over `k = 0..⌈m/n⌉`, denominator over
`k = 0..⌈m/n⌉ - 1`. -/
noncomputable def binomialBiroot (m n : ℕ) (x c : ℝ) : ℝ :=
  (∑ k ∈ Finset.range ((m + n - 1) / n + 1),
      x ^ k * c ^ (m - n * k) * (m.choose (n * k) : ℝ)) /
    (∑ k ∈ Finset.range ((m + n - 1) / n),
      x ^ k * c ^ (m - n * k - 1) * (m.choose (n * k + 1) : ℝ))

/-! ### Auxiliary lemmas -/

/-- `g ∣ (g - k + j)` exactly detects the residue class `j ≡ k (mod g)` when `k < g`. -/
private lemma dvd_shift_iff_mod_eq {g k : ℕ} (hg : 0 < g) (hk : k < g) (j : ℕ) :
    g ∣ (g - k + j) ↔ j % g = k := by
  constructor
  · rintro ⟨c, hc⟩
    match c, hc with
    | 0, hc => omega
    | (d + 1), hc =>
      have hmul : g * (d + 1) = g * d + g := by ring
      rw [hmul] at hc
      have hj : j = g * d + k := by omega
      rw [hj, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
  · intro h
    refine ⟨j / g + 1, ?_⟩
    have hdm := Nat.div_add_mod j g
    have hlt : j % g < g := Nat.mod_lt j hg
    rw [h] at hdm
    have he : g - k + j = g * (j / g) + g := by omega
    rw [he]; ring

/-- Evaluation of a real polynomial at a complex point as a finite coefficient sum. -/
private lemma aeval_complex_eq_sum_range (P : Polynomial ℝ) (z : ℂ) :
    Polynomial.aeval z P =
      ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℂ) * z ^ j := by
  rw [Polynomial.aeval_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => by rw [Complex.real_smul]

/-- A finite sum of channels with one unimodular channel and all others strictly
inside the unit disc converges to the distinguished channel's coefficient. -/
private lemma tendsto_channel_sum {g a₀ : ℕ} (ha₀ : a₀ ∈ Finset.range g) (c q : ℕ → ℂ)
    (hq0 : q a₀ = 1) (hq : ∀ a ∈ Finset.range g, a ≠ a₀ → ‖q a‖ < 1) :
    Filter.Tendsto (fun m : ℕ => ∑ a ∈ Finset.range g, c a * q a ^ m)
      Filter.atTop (nhds (c a₀)) := by
  have hsplit : ∀ m : ℕ, ∑ a ∈ Finset.range g, c a * q a ^ m
      = c a₀ + ∑ a ∈ (Finset.range g).erase a₀, c a * q a ^ m := by
    intro m
    rw [← Finset.add_sum_erase _ _ ha₀, hq0, one_pow, mul_one]
  simp only [hsplit]
  have hz : Filter.Tendsto
      (fun m : ℕ => ∑ a ∈ (Finset.range g).erase a₀, c a * q a ^ m)
      Filter.atTop (nhds 0) := by
    have := tendsto_finsetSum ((Finset.range g).erase a₀)
      (f := fun a => fun m : ℕ => c a * q a ^ m) (a := fun _ => (0 : ℂ))
      (fun i hi => by
        simpa using tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
            (hq i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))))
    simpa using this
  simpa using tendsto_const_nhds.add hz

/-- Evaluating a real polynomial at a real point, seen inside `ℂ`. -/
private lemma aeval_ofReal (P : Polynomial ℝ) (t : ℝ) :
    Polynomial.aeval ((t : ℂ)) P = ((Polynomial.eval t P : ℝ) : ℂ) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.eval_eq_sum_range]
  push_cast
  exact Finset.sum_congr rfl fun j _ => by rw [Complex.real_smul]

/-- Transfer of a limit of real numbers from its complex embedding. -/
private lemma tendsto_of_tendsto_ofReal {f : ℕ → ℝ} {L : ℝ}
    (h : Filter.Tendsto (fun m : ℕ => ((f m : ℂ))) Filter.atTop (nhds ((L : ℂ)))) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  have h' := (Complex.continuous_re.tendsto ((L : ℂ))).comp h
  simpa [Function.comp_def] using h'

/-! ### Rows, DAGs, and the filter -/

/-- **Target 1.** Pascal rows are the special case `P = (1+X)^N`. -/
theorem polySlice_one_add_X_pow (g r N : ℕ) (x : ℝ) :
    polySlice ((1 + Polynomial.X) ^ N) g r x = slice g r N x := by
  have h1 : (1 + Polynomial.X : Polynomial ℝ).natDegree = 1 := by
    rw [add_comm, ← Polynomial.C_1, Polynomial.natDegree_X_add_C]
  have hdeg : ((1 + Polynomial.X : Polynomial ℝ) ^ N).natDegree = N := by
    rw [Polynomial.natDegree_pow, h1, mul_one]
  unfold polySlice slice
  rw [hdeg]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_one_add_X_pow]

/-- **Target 2.** Any summation bound above the degree gives the same slice. -/
theorem polySlice_eq_sum_of_natDegree_lt (P : Polynomial ℝ) (g r : ℕ) (x : ℝ)
    {D : ℕ} (hD : P.natDegree < D) :
    polySlice P g r x =
      ∑ j ∈ Finset.range D, if j % g = r then P.coeff j * x ^ (j / g) else 0 := by
  refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
  · simp only [Finset.mem_range] at *; omega
  · simp only [Finset.mem_range, not_lt] at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, ite_self]

/-- **Target 3.** Linear DAG levels are convolution powers: level `m` is the coefficient
row of `basin * W^m`. -/
theorem dagNode_eq_coeff (basin : Polynomial ℝ) (w : List ℝ) (s m i : ℕ) :
    dagNode basin w s m i = (basin * dagWeightPoly w s ^ m).coeff i := by
  induction m generalizing i with
  | zero => simp [dagNode]
  | succ m ih =>
    rw [dagNode, pow_succ, ← mul_assoc]
    set Q := basin * dagWeightPoly w s ^ m with hQ
    rw [dagWeightPoly, Finset.mul_sum, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_C]
    split_ifs with h
    · rw [ih]; ring
    · ring

/-- **Target 4.** Roots-of-unity filter for an arbitrary real row. -/
theorem polySlice_roots_of_unity_filter {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) (P : Polynomial ℝ) (t : ℝ) :
    ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * Polynomial.aeval ((t : ℂ) * ω ^ a) P =
      (g : ℂ) * (t : ℂ) ^ k * (polySlice P g k (t ^ g) : ℂ) := by
  calc ∑ a ∈ Finset.range g, ω ^ (a * (g - k)) * Polynomial.aeval ((t : ℂ) * ω ^ a) P
      = ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℂ) * (t : ℂ) ^ j *
          ∑ a ∈ Finset.range g, ω ^ (a * (g - k + j)) := by
        simp only [aeval_complex_eq_sum_range, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
        rw [mul_pow, ← pow_mul, Nat.mul_add, pow_add]
        ring
    _ = (g : ℂ) * (t : ℂ) ^ k * (polySlice P g k (t ^ g) : ℂ) := by
        simp only [primitive_root_power_sum hω, dvd_shift_iff_mod_eq hg hk]
        rw [polySlice]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : j % g = k
        · simp only [h, if_true]
          have hj : j = k + g * (j / g) := by
            have := Nat.div_add_mod j g; omega
          rw [show ((t : ℂ)) ^ j = (t : ℂ) ^ k * ((t : ℂ) ^ g) ^ (j / g) by
            rw [← pow_mul, ← pow_add]; exact congrArg _ hj]
          push_cast
          ring
        · simp [h]

/-- Deviation of a filtered packet of `B * W^m` from its principal (real) channel:
the error is controlled by the subordinate channels of `B` and `W`. -/
private lemma polySlice_channel_deviation {g k' : ℕ} (hg : 0 < g) (hk' : k' < g)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) (t : ℝ) (B W : Polynomial ℝ) (m : ℕ) :
    |(g : ℝ) * t ^ k' * polySlice (B * W ^ m) g k' (t ^ g) -
        Polynomial.eval t B * Polynomial.eval t W ^ m|
      ≤ ∑ a ∈ (Finset.range g).erase 0,
          ‖Polynomial.aeval ((t : ℂ) * ω ^ a) B‖ *
            ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ ^ m := by
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hg.ne'
  have hfilter := polySlice_roots_of_unity_filter hg hk' hω (B * W ^ m) t
  have h0 : (0 : ℕ) ∈ Finset.range g := Finset.mem_range.mpr hg
  rw [← Finset.add_sum_erase _ _ h0] at hfilter
  simp only [Nat.zero_mul, pow_zero, one_mul, mul_one] at hfilter
  have hzero : Polynomial.aeval ((t : ℂ)) (B * W ^ m)
      = ((Polynomial.eval t B * Polynomial.eval t W ^ m : ℝ) : ℂ) := by
    rw [map_mul, map_pow, aeval_ofReal, aeval_ofReal]
    push_cast
    ring
  rw [hzero] at hfilter
  push_cast at hfilter
  have hdiff : (((g : ℝ) * t ^ k' * polySlice (B * W ^ m) g k' (t ^ g) -
        Polynomial.eval t B * Polynomial.eval t W ^ m : ℝ) : ℂ)
      = ∑ a ∈ (Finset.range g).erase 0,
          ω ^ (a * (g - k')) * Polynomial.aeval ((t : ℂ) * ω ^ a) (B * W ^ m) := by
    push_cast
    linear_combination -hfilter
  have habs : |(g : ℝ) * t ^ k' * polySlice (B * W ^ m) g k' (t ^ g) -
        Polynomial.eval t B * Polynomial.eval t W ^ m|
      = ‖∑ a ∈ (Finset.range g).erase 0,
          ω ^ (a * (g - k')) * Polynomial.aeval ((t : ℂ) * ω ^ a) (B * W ^ m)‖ := by
    rw [← hdiff, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun a _ => ?_)
  rw [map_mul, map_pow, norm_mul, norm_mul, norm_pow, norm_pow, hωnorm, one_pow, one_mul]

/-! ### Channel dominance -/

/-- **Target 5.** The slice ratio of `B * W^m` converges to the reciprocal power of the
strictly dominant channel `t ω^a₀`. -/
theorem tendsto_polySlice_ratio_of_dominant_channel
    {g k a₀ : ℕ} (hg : 0 < g) (hk : k < g) (ha₀ : a₀ < g)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) {t : ℝ} (ht : t ≠ 0)
    (B W : Polynomial ℝ)
    (hB : Polynomial.aeval ((t : ℂ) * ω ^ a₀) B ≠ 0)
    (hW : Polynomial.aeval ((t : ℂ) * ω ^ a₀) W ≠ 0)
    (hdom : ∀ a ∈ Finset.range g, a ≠ a₀ →
      ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ <
        ‖Polynomial.aeval ((t : ℂ) * ω ^ a₀) W‖) :
    Filter.Tendsto
      (fun m : ℕ => (polySlice (B * W ^ m) g k (t ^ g) : ℂ) /
        (polySlice (B * W ^ m) g 0 (t ^ g) : ℂ))
      Filter.atTop (nhds ((((t : ℂ) * ω ^ a₀) ^ k)⁻¹)) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hgne : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  set Wd : ℂ := Polynomial.aeval ((t : ℂ) * ω ^ a₀) W with hWd
  set Bv : ℕ → ℂ := fun a => Polynomial.aeval ((t : ℂ) * ω ^ a) B with hBv
  set Wv : ℕ → ℂ := fun a => Polynomial.aeval ((t : ℂ) * ω ^ a) W with hWv
  -- the roots-of-unity filter, specialised to the rows `B * W ^ m`
  have hid : ∀ k' : ℕ, k' < g → ∀ m : ℕ,
      ∑ a ∈ Finset.range g, (ω ^ (a * (g - k')) * Bv a) * Wv a ^ m
        = (g : ℂ) * (t : ℂ) ^ k' * (polySlice (B * W ^ m) g k' (t ^ g) : ℂ) := by
    intro k' hk' m
    rw [← polySlice_roots_of_unity_filter hg hk' hω (B * W ^ m) t]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_pow]
    ring
  set q : ℕ → ℂ := fun a => Wv a / Wd with hq
  have hq0 : q a₀ = 1 := div_self hW
  have hqlt : ∀ a ∈ Finset.range g, a ≠ a₀ → ‖q a‖ < 1 := by
    intro a ha hne
    rw [hq]
    simp only [norm_div]
    rw [div_lt_one (by simpa [hWd] using norm_pos_iff.mpr hW)]
    exact hdom a ha hne
  have hf : ∀ k' : ℕ, k' < g → ∀ m : ℕ,
      ∑ a ∈ Finset.range g, (ω ^ (a * (g - k')) * Bv a) * q a ^ m
        = ((g : ℂ) * (t : ℂ) ^ k' * (polySlice (B * W ^ m) g k' (t ^ g) : ℂ)) / Wd ^ m := by
    intro k' hk' m
    rw [← hid k' hk' m, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hq, div_pow, mul_div_assoc]
  have hlim1 := tendsto_channel_sum (Finset.mem_range.mpr ha₀)
    (fun a => ω ^ (a * (g - k)) * Bv a) q hq0 hqlt
  have hlim0 := tendsto_channel_sum (Finset.mem_range.mpr ha₀)
    (fun a => ω ^ (a * (g - 0)) * Bv a) q hq0 hqlt
  have hωg : ω ^ (a₀ * g) = 1 := by
    rw [mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hc0 : ω ^ (a₀ * (g - 0)) * Bv a₀ = Bv a₀ := by
    rw [Nat.sub_zero, hωg, one_mul]
  have hdiv := hlim1.div hlim0 (by rw [hc0]; exact hB)
  have key : ∀ m : ℕ,
      ((∑ a ∈ Finset.range g, (ω ^ (a * (g - k)) * Bv a) * q a ^ m) /
        (∑ a ∈ Finset.range g, (ω ^ (a * (g - 0)) * Bv a) * q a ^ m)) / (t : ℂ) ^ k
        = (polySlice (B * W ^ m) g k (t ^ g) : ℂ) /
          (polySlice (B * W ^ m) g 0 (t ^ g) : ℂ) := by
    intro m
    rw [hf k hk m, hf 0 hg m, div_div_div_cancel_right₀ (pow_ne_zero m hW),
      pow_zero, mul_one, mul_assoc, mul_div_mul_left _ _ hgne, mul_div_assoc,
      mul_div_cancel_left₀ _ (pow_ne_zero k htc)]
  have hval : (ω ^ (a₀ * (g - k)) * Bv a₀) / (ω ^ (a₀ * (g - 0)) * Bv a₀) / (t : ℂ) ^ k
      = (((t : ℂ) * ω ^ a₀) ^ k)⁻¹ := by
    rw [hc0, mul_div_cancel_right₀ _ hB]
    have hinv : ω ^ (a₀ * (g - k)) * ω ^ (a₀ * k) = 1 := by
      rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hk.le]
      exact hωg
    rw [eq_inv_of_mul_eq_one_left hinv, mul_pow, ← pow_mul, mul_inv, div_eq_mul_inv]
    ring
  rw [← hval]
  exact (hdiv.div_const ((t : ℂ) ^ k)).congr key

/-- **Target 6.** Real form: if the real channel dominates, the slice ratio of any
basin/weight row recovers `(t^k)⁻¹`, i.e. `x^(-k/g)` at `x = t^g`. -/
theorem tendsto_polySlice_ratio_of_dominance
    {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) {t : ℝ} (ht : 0 < t)
    (B W : Polynomial ℝ) (hB : Polynomial.eval t B ≠ 0) (hW : Polynomial.eval t W ≠ 0)
    (hdom : ∀ a ∈ Finset.range g, a ≠ 0 →
      ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ < |Polynomial.eval t W|) :
    Filter.Tendsto
      (fun m : ℕ => polySlice (B * W ^ m) g k (t ^ g) / polySlice (B * W ^ m) g 0 (t ^ g))
      Filter.atTop (nhds ((t ^ k)⁻¹)) := by
  have hz : ((t : ℂ) * ω ^ 0) = ((t : ℝ) : ℂ) := by rw [pow_zero, mul_one]
  have hB' : Polynomial.aeval ((t : ℂ) * ω ^ 0) B ≠ 0 := by
    rw [hz, aeval_ofReal]
    exact_mod_cast hB
  have hW' : Polynomial.aeval ((t : ℂ) * ω ^ 0) W ≠ 0 := by
    rw [hz, aeval_ofReal]
    exact_mod_cast hW
  have hdom' : ∀ a ∈ Finset.range g, a ≠ 0 →
      ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ < ‖Polynomial.aeval ((t : ℂ) * ω ^ 0) W‖ := by
    intro a ha hne
    rw [hz, aeval_ofReal, Complex.norm_real, Real.norm_eq_abs]
    exact hdom a ha hne
  have h := tendsto_polySlice_ratio_of_dominant_channel hg hk hg hω ht.ne' B W hB' hW' hdom'
  rw [hz] at h
  refine tendsto_of_tendsto_ofReal ?_
  have hlim : (((t : ℝ) : ℂ) ^ k)⁻¹ = (((t ^ k)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [← hlim]
  refine h.congr fun m => ?_
  push_cast
  ring

/-- **Target 7.** Geometric rate: the error is `O(ρ^m)` for any `ρ < 1` bounding the
subordinate channel ratios; the basin only affects the constant. -/
theorem polySlice_ratio_geometric_rate
    {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g) {t : ℝ} (ht : 0 < t)
    (B W : Polynomial ℝ) (hB : Polynomial.eval t B ≠ 0) (hW : Polynomial.eval t W ≠ 0)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hρ : ∀ a ∈ Finset.range g, a ≠ 0 →
      ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ ≤ ρ * |Polynomial.eval t W|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M₀ : ℕ, ∀ m ≥ M₀,
      |polySlice (B * W ^ m) g k (t ^ g) / polySlice (B * W ^ m) g 0 (t ^ g) - (t ^ k)⁻¹|
        ≤ C * ρ ^ m := by
  set V := Polynomial.eval t W with hVdef
  set B₀ := Polynomial.eval t B with hB₀def
  set K := ∑ a ∈ (Finset.range g).erase 0, ‖Polynomial.aeval ((t : ℂ) * ω ^ a) B‖ with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun a _ => norm_nonneg _
  have hB0pos : 0 < |B₀| := abs_pos.mpr hB
  have hVabs : 0 < |V| := abs_pos.mpr hW
  have hdev : ∀ k' : ℕ, k' < g → ∀ m : ℕ,
      |(g : ℝ) * t ^ k' * polySlice (B * W ^ m) g k' (t ^ g) - B₀ * V ^ m|
        ≤ K * (ρ ^ m * |V| ^ m) := by
    intro k' hk' m
    refine le_trans (polySlice_channel_deviation hg hk' hω t B W m) ?_
    have hterm : ∀ a ∈ (Finset.range g).erase 0,
        ‖Polynomial.aeval ((t : ℂ) * ω ^ a) B‖ *
            ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ ^ m
          ≤ ‖Polynomial.aeval ((t : ℂ) * ω ^ a) B‖ * (ρ ^ m * |V| ^ m) := by
      intro a ha
      have h1 := hρ a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 m
      rw [mul_pow] at h2
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul, ← hKdef]
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ m ≥ M₀, K * ρ ^ m ≤ |B₀| / 2 := by
    have hpow : Filter.Tendsto (fun m : ℕ => K * ρ ^ m) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1)
    exact Filter.eventually_atTop.mp
      (hpow.eventually_le_const (by positivity : (0 : ℝ) < |B₀| / 2))
  refine ⟨4 * K / (t ^ k * |B₀|), by positivity, M₀, fun m hm => ?_⟩
  have hVm : (0 : ℝ) < |V| ^ m := pow_pos hVabs m
  have htk : (0 : ℝ) < t ^ k := pow_pos ht k
  have hu := hdev k hk m
  have hv := hdev 0 hg m
  rw [pow_zero, mul_one] at hv
  have hKm : K * (ρ ^ m * |V| ^ m) ≤ |B₀| / 2 * |V| ^ m := by
    have h := hM₀ m hm
    nlinarith [hVm]
  have habsBV : |B₀ * V ^ m| = |B₀| * |V| ^ m := by rw [abs_mul, abs_pow]
  have hvlb : |B₀| / 2 * |V| ^ m ≤ |(g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g)| := by
    have h1 := abs_sub_abs_le_abs_sub (B₀ * V ^ m)
      ((g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g))
    rw [habsBV, abs_sub_comm (B₀ * V ^ m)] at h1
    have h2 : |(g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g) - B₀ * V ^ m|
        ≤ |B₀| / 2 * |V| ^ m := le_trans hv hKm
    linarith
  have hS0 : polySlice (B * W ^ m) g 0 (t ^ g) ≠ 0 := by
    intro h
    rw [h, mul_zero, abs_zero] at hvlb
    nlinarith
  have hgne : (g : ℝ) ≠ 0 := by positivity
  have hratio : polySlice (B * W ^ m) g k (t ^ g) / polySlice (B * W ^ m) g 0 (t ^ g)
        - (t ^ k)⁻¹
      = ((g : ℝ) * t ^ k * polySlice (B * W ^ m) g k (t ^ g)
          - (g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g)) /
        (t ^ k * ((g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g))) := by
    field_simp
  have hnum : |(g : ℝ) * t ^ k * polySlice (B * W ^ m) g k (t ^ g)
      - (g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g)| ≤ 2 * (K * (ρ ^ m * |V| ^ m)) := by
    calc |(g : ℝ) * t ^ k * polySlice (B * W ^ m) g k (t ^ g)
            - (g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g)|
        ≤ |(g : ℝ) * t ^ k * polySlice (B * W ^ m) g k (t ^ g) - B₀ * V ^ m| +
          |B₀ * V ^ m - (g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g)| := abs_sub_le _ _ _
      _ ≤ K * (ρ ^ m * |V| ^ m) + K * (ρ ^ m * |V| ^ m) := by
          rw [abs_sub_comm (B₀ * V ^ m)]
          exact add_le_add hu hv
      _ = 2 * (K * (ρ ^ m * |V| ^ m)) := by ring
  rw [hratio, abs_div, abs_mul, abs_of_pos htk,
    div_le_iff₀ (by positivity :
      (0 : ℝ) < t ^ k * |(g : ℝ) * polySlice (B * W ^ m) g 0 (t ^ g)|)]
  have hstep : 2 * (K * (ρ ^ m * |V| ^ m))
      = 4 * K / (t ^ k * |B₀|) * ρ ^ m * (t ^ k * ((|B₀| / 2) * |V| ^ m)) := by
    field_simp
    ring
  rw [hstep] at hnum
  refine le_trans hnum ?_
  have hc : (0 : ℝ) ≤ 4 * K / (t ^ k * |B₀|) * ρ ^ m * t ^ k := by positivity
  nlinarith [hvlb, hc]

/-! ### Nonnegative weights: dominance is phase separation -/

/-- The real part of `conj v * w` for unit vectors `v`, `w` never exceeds `1`. -/
private lemma re_conj_mul_le_one {v w : ℂ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ((starRingEnd ℂ) v * w).re ≤ 1 := by
  have hnorm : ‖(starRingEnd ℂ) v * w‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, hv, hw, one_mul]
  calc ((starRingEnd ℂ) v * w).re ≤ ‖(starRingEnd ℂ) v * w‖ := Complex.re_le_norm _
    _ = 1 := hnorm

/-- Distinct unit vectors have `Re (conj v * w) < 1`. -/
private lemma re_conj_mul_lt_one {v w : ℂ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hne : v ≠ w) :
    ((starRingEnd ℂ) v * w).re < 1 := by
  rcases lt_or_eq_of_le (re_conj_mul_le_one hv hw) with h | h
  · exact h
  · exfalso
    set z : ℂ := (starRingEnd ℂ) v * w with hzdef
    have hnorm : ‖z‖ = 1 := by
      rw [hzdef, norm_mul, Complex.norm_conj, hv, hw, one_mul]
    have h2 := Complex.normSq_apply z
    rw [Complex.normSq_eq_norm_sq, hnorm, one_pow] at h2
    have him : z.im = 0 := by nlinarith [h, h2, sq_nonneg z.im]
    have hz1 : z = 1 := Complex.ext (by rw [h]; rfl) (by rw [him]; rfl)
    have hvv : v * (starRingEnd ℂ) v = 1 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hv, one_pow]
    have hwv : w = v := by
      have hc := congrArg (fun x => v * x) hz1
      simp only [hzdef] at hc
      rw [← mul_assoc, hvv, one_mul, mul_one] at hc
      exact hc
    exact hne hwv.symm

/-- **Target 8.** Two nonzero weights with distinct phases give strict dominance. -/
theorem nonneg_weights_channel_lt
    {g a : ℕ} (hg : 0 < g) {ω : ℂ} (hω : IsPrimitiveRoot ω g) {t : ℝ} (ht : 0 < t)
    (W : Polynomial ℝ) (hW : ∀ i, 0 ≤ W.coeff i)
    (hsep : ∃ i j, W.coeff i ≠ 0 ∧ W.coeff j ≠ 0 ∧ ω ^ (a * i) ≠ ω ^ (a * j)) :
    ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ < Polynomial.eval t W := by
  obtain ⟨i, j, hi, hj, hij⟩ := hsep
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hg.ne'
  have hunit : ∀ n : ℕ, ‖ω ^ (a * n)‖ = 1 := fun n => by rw [norm_pow, hωnorm, one_pow]
  set D := W.natDegree
  have hiD : i ∈ Finset.range (D + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hi))
  have hjD : j ∈ Finset.range (D + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hj))
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ W.coeff n * t ^ n := fun n =>
    mul_nonneg (hW n) (pow_nonneg ht.le n)
  have hipos : 0 < W.coeff i * t ^ i :=
    mul_pos (lt_of_le_of_ne (hW i) (Ne.symm hi)) (pow_pos ht i)
  have hjpos : 0 < W.coeff j * t ^ j :=
    mul_pos (lt_of_le_of_ne (hW j) (Ne.symm hj)) (pow_pos ht j)
  have hS : Polynomial.eval t W = ∑ n ∈ Finset.range (D + 1), W.coeff n * t ^ n :=
    Polynomial.eval_eq_sum_range t
  have hZ : Polynomial.aeval ((t : ℂ) * ω ^ a) W
      = ∑ n ∈ Finset.range (D + 1), ((W.coeff n * t ^ n : ℝ) : ℂ) * ω ^ (a * n) := by
    rw [Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.real_smul, mul_pow, ← pow_mul]
    push_cast
    ring
  have hreal : ∀ (u : ℂ) (n : ℕ),
      ((starRingEnd ℂ) u * (((W.coeff n * t ^ n : ℝ) : ℂ) * ω ^ (a * n))).re
        = (W.coeff n * t ^ n) * ((starRingEnd ℂ) u * ω ^ (a * n)).re := by
    intro u n
    rw [show (starRingEnd ℂ) u * (((W.coeff n * t ^ n : ℝ) : ℂ) * ω ^ (a * n))
        = ((W.coeff n * t ^ n : ℝ) : ℂ) * ((starRingEnd ℂ) u * ω ^ (a * n)) by ring,
      Complex.re_ofReal_mul]
  set Z : ℂ := Polynomial.aeval ((t : ℂ) * ω ^ a) W with hZdef
  by_cases hZ0 : Z = 0
  · rw [hZ0, norm_zero, hS]
    exact lt_of_lt_of_le hipos (Finset.single_le_sum (fun n _ => hterm_nonneg n) hiD)
  · set u : ℂ := Z / ((‖Z‖ : ℝ) : ℂ) with hu
    have hZnorm : (0 : ℝ) < ‖Z‖ := norm_pos_iff.mpr hZ0
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZnorm,
        div_self hZnorm.ne']
    have hconj : (starRingEnd ℂ) u * Z = ((‖Z‖ : ℝ) : ℂ) := by
      rw [hu, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div,
        mul_comm ((starRingEnd ℂ) Z) Z, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp
    have hre : ‖Z‖ = ((starRingEnd ℂ) u * Z).re := by rw [hconj, Complex.ofReal_re]
    rw [hre, hZ, Finset.mul_sum, Complex.re_sum, hS]
    refine Finset.sum_lt_sum (fun n _ => ?_) ?_
    · rw [hreal u n]
      nlinarith [hterm_nonneg n, re_conj_mul_le_one hunorm (hunit n)]
    · have hne : u ≠ ω ^ (a * i) ∨ u ≠ ω ^ (a * j) := by
        by_cases h : u = ω ^ (a * i)
        · exact Or.inr fun h2 => hij (h.symm.trans h2)
        · exact Or.inl h
      have hstrict : ∀ n : ℕ, u ≠ ω ^ (a * n) → 0 < W.coeff n * t ^ n →
          n ∈ Finset.range (D + 1) →
          ∃ n ∈ Finset.range (D + 1),
            ((starRingEnd ℂ) u * (((W.coeff n * t ^ n : ℝ) : ℂ) * ω ^ (a * n))).re
              < W.coeff n * t ^ n := by
        intro n hun hpos hmem
        refine ⟨n, hmem, ?_⟩
        rw [hreal u n]
        nlinarith [re_conj_mul_lt_one hunorm (hunit n) hun, hpos]
      rcases hne with h | h
      · exact hstrict i h hipos hiD
      · exact hstrict j h hjpos hjD

/-- **Target 9.** If all nonzero weights share one phase, the channel ties the real one. -/
theorem nonneg_weights_channel_eq
    {g a : ℕ} (hg : 0 < g) {ω : ℂ} (hω : IsPrimitiveRoot ω g) {t : ℝ} (ht : 0 < t)
    (W : Polynomial ℝ) (hW : ∀ i, 0 ≤ W.coeff i)
    (htie : ∀ i j, W.coeff i ≠ 0 → W.coeff j ≠ 0 → ω ^ (a * i) = ω ^ (a * j)) :
    ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ = Polynomial.eval t W := by
  have hωnorm : ‖ω‖ = 1 := hω.norm'_eq_one hg.ne'
  set D := W.natDegree
  have hS : Polynomial.eval t W = ∑ n ∈ Finset.range (D + 1), W.coeff n * t ^ n :=
    Polynomial.eval_eq_sum_range t
  have hSnonneg : 0 ≤ Polynomial.eval t W := by
    rw [hS]
    exact Finset.sum_nonneg fun n _ => mul_nonneg (hW n) (pow_nonneg ht.le n)
  have hZ : Polynomial.aeval ((t : ℂ) * ω ^ a) W
      = ∑ n ∈ Finset.range (D + 1), ((W.coeff n * t ^ n : ℝ) : ℂ) * ω ^ (a * n) := by
    rw [Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.real_smul, mul_pow, ← pow_mul]
    push_cast
    ring
  by_cases hW0 : W = 0
  · subst hW0
    simp
  · have hlead : W.coeff D ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hW0
    have hfac : Polynomial.aeval ((t : ℂ) * ω ^ a) W
        = ω ^ (a * D) * ((Polynomial.eval t W : ℝ) : ℂ) := by
      rw [hZ, hS]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hc : W.coeff n = 0
      · rw [hc]; push_cast; ring
      · rw [htie n D hc hlead]; ring
    rw [hfac, norm_mul, norm_pow, hωnorm, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hSnonneg]

/-- **Target 10.** For nonnegative weights, real-channel dominance holds iff every
nontrivial channel separates the phases of some pair of nonzero weights. -/
theorem nonneg_weights_dominance_iff
    {g : ℕ} (hg : 0 < g) {ω : ℂ} (hω : IsPrimitiveRoot ω g) {t : ℝ} (ht : 0 < t)
    (W : Polynomial ℝ) (hW : ∀ i, 0 ≤ W.coeff i) :
    (∀ a ∈ Finset.range g, a ≠ 0 →
        ‖Polynomial.aeval ((t : ℂ) * ω ^ a) W‖ < Polynomial.eval t W) ↔
      (∀ a ∈ Finset.range g, a ≠ 0 →
        ∃ i j, W.coeff i ≠ 0 ∧ W.coeff j ≠ 0 ∧ ω ^ (a * i) ≠ ω ^ (a * j)) := by
  constructor
  · intro hlt a ha ha0
    by_contra hcon
    have htie : ∀ i j, W.coeff i ≠ 0 → W.coeff j ≠ 0 → ω ^ (a * i) = ω ^ (a * j) := by
      intro i j hi hj
      by_contra hne
      exact hcon ⟨i, j, hi, hj, hne⟩
    exact absurd (nonneg_weights_channel_eq hg hω ht W hW htie) (ne_of_lt (hlt a ha ha0))
  · intro hsep a ha ha0
    exact nonneg_weights_channel_lt hg hω ht W hW (hsep a ha ha0)

/-! ### Sharpness: the hypotheses cannot be dropped -/

/-- Splitting a sum of even length into its even and odd halves. -/
private lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range (2 * n), f j = ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ← ih, add_assoc]

/-- Even coefficients of the skip weight `(1 + X^2)^m`. -/
private lemma coeff_sq_pow_even (m i : ℕ) :
    ((1 + Polynomial.X ^ 2 : Polynomial ℝ) ^ m).coeff (2 * i) = (m.choose i : ℝ) := by
  induction m generalizing i with
  | zero =>
    rcases i with _ | j
    · simp
    · simp [Polynomial.coeff_one, Nat.choose]
  | succ m ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', ih]
    rcases i with _ | j
    · norm_num
    · rw [if_pos (by omega), show 2 * (j + 1) - 2 = 2 * j by omega, ih, Nat.choose_succ_succ]
      push_cast
      ring

/-- Odd coefficients of the skip weight `(1 + X^2)^m` vanish. -/
private lemma coeff_sq_pow_odd (m i : ℕ) :
    ((1 + Polynomial.X ^ 2 : Polynomial ℝ) ^ m).coeff (2 * i + 1) = 0 := by
  induction m generalizing i with
  | zero => simp [Polynomial.coeff_one]
  | succ m ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', ih]
    rcases i with _ | j
    · norm_num
    · rw [if_pos (by omega), show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega, ih]
      ring

/-- **Target 11.** Skip rows (`W = 1 + X^2`, basin `1 + X`) at `g = 2`: both slices are
`(1+x)^m` exactly, so the ratio is identically `1`. -/
theorem skipRow_slices (m : ℕ) (x : ℝ) :
    polySlice ((1 + Polynomial.X) * (1 + Polynomial.X ^ 2) ^ m) 2 0 x = (1 + x) ^ m ∧
      polySlice ((1 + Polynomial.X) * (1 + Polynomial.X ^ 2) ^ m) 2 1 x = (1 + x) ^ m := by
  set Q : Polynomial ℝ := (1 + Polynomial.X ^ 2) ^ m with hQ
  have hsplit : (1 + Polynomial.X : Polynomial ℝ) * Q = Q + Polynomial.X * Q := by
    rw [add_mul, one_mul]
  have hPeven : ∀ i : ℕ, ((1 + Polynomial.X : Polynomial ℝ) * Q).coeff (2 * i)
      = (m.choose i : ℝ) := by
    intro i
    rw [hsplit, Polynomial.coeff_add, hQ, coeff_sq_pow_even]
    rcases i with _ | j
    · simp [Polynomial.mul_coeff_zero]
    · rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Polynomial.coeff_X_mul,
        coeff_sq_pow_odd, add_zero]
  have hPodd : ∀ i : ℕ, ((1 + Polynomial.X : Polynomial ℝ) * Q).coeff (2 * i + 1)
      = (m.choose i : ℝ) := by
    intro i
    rw [hsplit, Polynomial.coeff_add, hQ, coeff_sq_pow_odd, Polynomial.coeff_X_mul,
      coeff_sq_pow_even, zero_add]
  have hD : ((1 + Polynomial.X : Polynomial ℝ) * Q).natDegree < 2 * (m + 1) := by
    have h1 : (1 + Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
      rw [add_comm, ← Polynomial.C_1, Polynomial.natDegree_X_add_C]
    have h2 : Q.natDegree ≤ 2 * m := by
      rw [hQ]
      refine le_trans Polynomial.natDegree_pow_le ?_
      have hd2 : (1 + Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) ?_
        simp
      calc m * (1 + Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ m * 2 :=
            Nat.mul_le_mul_left m hd2
        _ = 2 * m := by ring
    have h3 := Polynomial.natDegree_mul_le (p := (1 + Polynomial.X : Polynomial ℝ)) (q := Q)
    omega
  have hbinom : (1 + x) ^ m = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * x ^ i := by
    rw [add_comm, add_pow]
    exact Finset.sum_congr rfl fun i _ => by rw [one_pow, mul_one]; ring
  constructor
  · rw [polySlice_eq_sum_of_natDegree_lt _ 2 0 x hD, sum_range_two_mul, hbinom]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (by omega), if_neg (by omega), add_zero, hPeven,
      show 2 * i / 2 = i by omega]
  · rw [polySlice_eq_sum_of_natDegree_lt _ 2 1 x hD, sum_range_two_mul, hbinom]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_neg (by omega), if_pos (by omega), zero_add, hPodd,
      show (2 * i + 1) / 2 = i by omega]

/-- **Target 12.** Hence skip rows do not recover the root: at `x = 2^2` the ratio does
not tend to `2⁻¹`. -/
theorem skipRow_ratio_not_tendsto :
    ¬ Filter.Tendsto
      (fun m : ℕ =>
        polySlice ((1 + Polynomial.X) * (1 + Polynomial.X ^ 2) ^ m) 2 1 ((2 : ℝ) ^ 2) /
          polySlice ((1 + Polynomial.X) * (1 + Polynomial.X ^ 2) ^ m) 2 0 ((2 : ℝ) ^ 2))
      Filter.atTop (nhds (((2 : ℝ) ^ 1)⁻¹)) := by
  intro h
  have hconst : (fun m : ℕ =>
      polySlice ((1 + Polynomial.X) * (1 + Polynomial.X ^ 2) ^ m) 2 1 ((2 : ℝ) ^ 2) /
        polySlice ((1 + Polynomial.X) * (1 + Polynomial.X ^ 2) ^ m) 2 0 ((2 : ℝ) ^ 2))
      = fun _ : ℕ => (1 : ℝ) := by
    funext m
    rw [(skipRow_slices m ((2 : ℝ) ^ 2)).1, (skipRow_slices m ((2 : ℝ) ^ 2)).2]
    exact div_self (by positivity)
  rw [hconst] at h
  have huniq := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at huniq

/-- **Target 13.** Mixed-sign weights `W = 1 - X + X^2` hand dominance to the `-t`
channel: the square-root slice ratio converges to `-t⁻¹` instead of `t⁻¹`. -/
theorem mixedSign_ratio_tendsto_neg {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto
      (fun m : ℕ =>
        polySlice ((1 - Polynomial.X + Polynomial.X ^ 2) ^ m) 2 1 (t ^ 2) /
          polySlice ((1 - Polynomial.X + Polynomial.X ^ 2) ^ m) 2 0 (t ^ 2))
      Filter.atTop (nhds (-t⁻¹)) := by
  have hω : IsPrimitiveRoot (-1 : ℂ) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hev : ∀ z : ℂ,
      Polynomial.aeval z (1 - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℝ)
        = 1 - z + z ^ 2 := by
    intro z; simp
  have hz1 : ((t : ℂ) * (-1) ^ 1) = ((-t : ℝ) : ℂ) := by norm_num
  have hz0 : ((t : ℂ) * (-1) ^ 0) = ((t : ℝ) : ℂ) := by norm_num
  have hW1 : Polynomial.aeval ((t : ℂ) * (-1 : ℂ) ^ 1)
      (1 - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℝ) = ((1 + t + t ^ 2 : ℝ) : ℂ) := by
    rw [hz1, hev]; push_cast; ring
  have hW0 : Polynomial.aeval ((t : ℂ) * (-1 : ℂ) ^ 0)
      (1 - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℝ) = ((1 - t + t ^ 2 : ℝ) : ℂ) := by
    rw [hz0, hev]; push_cast; ring
  have hpos1 : (0 : ℝ) < 1 + t + t ^ 2 := by positivity
  have hpos0 : (0 : ℝ) < 1 - t + t ^ 2 := by nlinarith [sq_nonneg (t - 1), sq_nonneg t]
  have hB : Polynomial.aeval ((t : ℂ) * (-1 : ℂ) ^ 1) (1 : Polynomial ℝ) ≠ 0 := by
    rw [map_one]; exact one_ne_zero
  have hWne : Polynomial.aeval ((t : ℂ) * (-1 : ℂ) ^ 1)
      (1 - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
    rw [hW1]
    exact_mod_cast hpos1.ne'
  have hdom : ∀ a ∈ Finset.range 2, a ≠ 1 →
      ‖Polynomial.aeval ((t : ℂ) * (-1 : ℂ) ^ a)
          (1 - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℝ)‖ <
        ‖Polynomial.aeval ((t : ℂ) * (-1 : ℂ) ^ 1)
          (1 - Polynomial.X + Polynomial.X ^ 2 : Polynomial ℝ)‖ := by
    intro a ha hne
    have ha0 : a = 0 := by
      have := Finset.mem_range.mp ha
      omega
    subst ha0
    rw [hW0, hW1, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hpos0, abs_of_pos hpos1]
    linarith
  have h := tendsto_polySlice_ratio_of_dominant_channel (g := 2) (k := 1) (a₀ := 1)
    (by norm_num) (by norm_num) (by norm_num) hω ht.ne' 1
    (1 - Polynomial.X + Polynomial.X ^ 2) hB hWne hdom
  simp only [one_mul] at h
  rw [hz1] at h
  refine tendsto_of_tendsto_ofReal ?_
  have hlim : ((((-t : ℝ)) : ℂ) ^ 1)⁻¹ = ((-t⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [pow_one]
    field_simp
  rw [← hlim]
  refine h.congr fun m => ?_
  push_cast
  ring

/-! ### The binomial biroot (arXiv:2508.14095) -/

/-- Reindexing a residue class `j ≡ r (mod n)` of `range (m+1)` by `j = n*k + r`. -/
private lemma sum_residue_reindex {n r m L : ℕ} (hn : 0 < n) (hr : r < n) (F : ℕ → ℝ)
    (hvanish : ∀ k, m < n * k + r → F k = 0)
    (hL : ∀ k, n * k + r ≤ m → k < L) :
    ∑ j ∈ Finset.range (m + 1), (if j % n = r then F (j / n) else 0)
      = ∑ k ∈ Finset.range L, F k := by
  rw [← Finset.sum_filter]
  have hright : ∑ k ∈ Finset.range L, F k
      = ∑ k ∈ (Finset.range L).filter (fun k => n * k + r ≤ m), F k := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_range] at hk hk'
    exact hvanish k (by omega)
  rw [hright]
  refine Finset.sum_nbij' (fun j => j / n) (fun k => n * k + r) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj1, hj2⟩ := hj
    have hdm := Nat.div_add_mod j n
    rw [hj2] at hdm
    have hle : n * (j / n) + r ≤ m := by omega
    exact ⟨hL _ hle, hle⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    have hdm := Nat.div_add_mod j n
    rw [hj.2] at hdm
    omega
  · intro k _
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.add_zero]
  · intro j _
    rfl

/-- **Target 14.** Wolford's binomial biroot is a rescaled residue-slice ratio. -/
theorem binomialBiroot_eq_slice_ratio {m n : ℕ} (hn : 2 ≤ n) {x c : ℝ} (hc : 0 < c) :
    binomialBiroot m n x c =
      c * slice n 0 m (x / c ^ n) / slice n 1 m (x / c ^ n) := by
  have hn0 : 0 < n := by omega
  set y : ℝ := x / c ^ n with hy
  set K : ℕ := (m + n - 1) / n with hK
  have hcy : ∀ M k : ℕ, n * k ≤ M → c ^ M * y ^ k = x ^ k * c ^ (M - n * k) := by
    intro M k hk
    have h1 : c ^ (M - n * k) * c ^ (n * k) = c ^ M := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have h2 : y ^ k = x ^ k / c ^ (n * k) := by rw [hy, div_pow, ← pow_mul]
    have hcne : (c : ℝ) ^ (n * k) ≠ 0 := pow_ne_zero _ hc.ne'
    calc c ^ M * y ^ k = (c ^ (M - n * k) * c ^ (n * k)) * (x ^ k / c ^ (n * k)) := by
          rw [h1, h2]
      _ = x ^ k * c ^ (M - n * k) := by field_simp
  have hA : c ^ m * slice n 0 m y
      = ∑ k ∈ Finset.range (K + 1), x ^ k * c ^ (m - n * k) * (m.choose (n * k) : ℝ) := by
    rw [slice, Finset.mul_sum]
    rw [Finset.sum_congr rfl (g := fun j => if j % n = 0 then
        (fun k => x ^ k * c ^ (m - n * k) * (m.choose (n * k) : ℝ)) (j / n) else 0) ?_]
    · refine sum_residue_reindex (r := 0) (m := m) (L := K + 1) hn0 hn0
        (fun k => x ^ k * c ^ (m - n * k) * (m.choose (n * k) : ℝ)) ?_ ?_
      · intro k hk
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        push_cast
        ring
      · intro k hk
        have h1 : k ≤ m / n := (Nat.le_div_iff_mul_le hn0).mpr (by rw [mul_comm]; omega)
        have h2 : m / n ≤ K := by
          rw [hK]
          exact Nat.div_le_div_right (by omega)
        omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      by_cases hjr : j % n = 0
      · rw [if_pos hjr, if_pos hjr]
        have hnj : n * (j / n) = j := by
          have := Nat.div_add_mod j n
          omega
        have hstep : c ^ m * y ^ (j / n) = x ^ (j / n) * c ^ (m - j) := by
          have h := hcy m (j / n) (by omega)
          rwa [hnj] at h
        show c ^ m * ((m.choose j : ℝ) * y ^ (j / n))
          = x ^ (j / n) * c ^ (m - n * (j / n)) * (m.choose (n * (j / n)) : ℝ)
        rw [hnj, show c ^ m * ((m.choose j : ℝ) * y ^ (j / n))
          = (m.choose j : ℝ) * (c ^ m * y ^ (j / n)) by ring, hstep]
        ring
      · rw [if_neg hjr, if_neg hjr, mul_zero]
  have hB : c ^ (m - 1) * slice n 1 m y
      = ∑ k ∈ Finset.range K, x ^ k * c ^ (m - n * k - 1) * (m.choose (n * k + 1) : ℝ) := by
    rw [slice, Finset.mul_sum]
    rw [Finset.sum_congr rfl (g := fun j => if j % n = 1 then
        (fun k => x ^ k * c ^ (m - n * k - 1) * (m.choose (n * k + 1) : ℝ)) (j / n) else 0) ?_]
    · refine sum_residue_reindex (r := 1) (m := m) (L := K) hn0 (by omega)
        (fun k => x ^ k * c ^ (m - n * k - 1) * (m.choose (n * k + 1) : ℝ)) ?_ ?_
      · intro k hk
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        push_cast
        ring
      · intro k hk
        have hm1 : 1 ≤ m := by omega
        have h1 : k ≤ (m - 1) / n := (Nat.le_div_iff_mul_le hn0).mpr (by rw [mul_comm]; omega)
        have h2 : K = (m - 1) / n + 1 := by
          rw [hK, show m + n - 1 = (m - 1) + n by omega, Nat.add_div_right _ hn0]
        omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      by_cases hjr : j % n = 1
      · rw [if_pos hjr, if_pos hjr]
        have hnj : n * (j / n) + 1 = j := by
          have := Nat.div_add_mod j n
          omega
        have hstep : c ^ (m - 1) * y ^ (j / n) = x ^ (j / n) * c ^ (m - j) := by
          have h := hcy (m - 1) (j / n) (by omega)
          rwa [show m - 1 - n * (j / n) = m - j by omega] at h
        show c ^ (m - 1) * ((m.choose j : ℝ) * y ^ (j / n))
          = x ^ (j / n) * c ^ (m - n * (j / n) - 1) * (m.choose (n * (j / n) + 1) : ℝ)
        rw [hnj, show m - n * (j / n) - 1 = m - j by omega,
          show c ^ (m - 1) * ((m.choose j : ℝ) * y ^ (j / n))
            = (m.choose j : ℝ) * (c ^ (m - 1) * y ^ (j / n)) by ring, hstep]
        ring
      · rw [if_neg hjr, if_neg hjr, mul_zero]
  rw [binomialBiroot, ← hA, ← hB]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hz : slice n 1 0 y = 0 := by simp [slice]
    rw [hz]
    simp
  · have hcm : c ^ m = c * c ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hcm, show c * c ^ (m - 1) * slice n 0 m y = c ^ (m - 1) * (c * slice n 0 m y) by ring]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hc.ne')

/-- **Target 15.** The generalized binomial biroot conjecture (arXiv:2508.14095,
Conjecture 3.4): `β_m^n(x, c) → x^(1/n)` for every `n ≥ 2`, `x > 0`, `c > 0`. -/
theorem tendsto_binomialBiroot {n : ℕ} (hn : 2 ≤ n) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Filter.Tendsto (fun m : ℕ => binomialBiroot m n x c) Filter.atTop
      (nhds (x ^ ((n : ℝ)⁻¹))) := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  set y : ℝ := x / c ^ n with hy
  have hypos : 0 < y := div_pos hx (pow_pos hc n)
  have h := tendsto_slice_ratio_rpow (g := n) (k := 1) hn0 hn1 hypos
  set L : ℝ := y ^ (-(1 : ℕ) / (n : ℝ)) with hLdef
  have hLpos : 0 < L := Real.rpow_pos_of_pos hypos _
  have hinv := h.inv₀ hLpos.ne'
  have hmul := hinv.const_mul c
  have hlimit : c * L⁻¹ = x ^ ((n : ℝ)⁻¹) := by
    have h1 : L = (y ^ ((n : ℝ)⁻¹))⁻¹ := by
      rw [hLdef, show (-(1 : ℕ) / (n : ℝ)) = -((n : ℝ)⁻¹) by push_cast; ring,
        Real.rpow_neg hypos.le]
    have h2 : y ^ ((n : ℝ)⁻¹) = x ^ ((n : ℝ)⁻¹) / c := by
      rw [hy, Real.div_rpow hx.le (pow_nonneg hc.le n), ← Real.rpow_natCast c n,
        ← Real.rpow_mul hc.le, mul_inv_cancel₀ (by positivity : (n : ℝ) ≠ 0), Real.rpow_one]
    rw [h1, inv_inv, h2]
    field_simp
  rw [← hlimit]
  refine hmul.congr fun m => ?_
  rw [binomialBiroot_eq_slice_ratio hn hc, inv_div, mul_div_assoc]

end ResidueSlices
