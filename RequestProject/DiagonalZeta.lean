/-
Target statements for Aristotle: the uniform diagonal suppression lemma and
the resulting uniform diagonal slice-ratio estimate, following
Lemma [Uniform off-axis suppression on the diagonal] and the diagonal
estimate in `residue_packetization.tex`.

Build on the existing development plus the two attached verified files
(`ExplicitSpectralRate.lean`, `RpowCorollaries.lean` — add them to
RequestProject unchanged; they build cleanly against this project).
Key available tools: `channelRatio`, `spectralGap`,
`channelRatio_le_spectralGap`, `spectralGap_mem_unitInterval`
(QuantitativeSpectralGap.lean) and `slice_ratio_explicit_rate_rpow`
(RpowCorollaries.lean).

Proof route from the paper for the suppression lemma: with `t = n^(1/g)` and
`θ` the argument of `ω^a`,
  `‖1 + t·ω^a‖² = (1+t)² − 2(1−cos θ)·t`,
so `channelRatio = √(1 − 2(1−cos θ)t/(1+t)²) ≤ exp(−(1−cos θ)t/(1+t)²)`;
for `1 ≤ t ≤ N^(1/g)` one has `t/(1+t)² ≥ N^(−1/g)/4`, and
`1 − cos θ ≥ 1 − cos(2π/g)` for any nontrivial power of a primitive root,
giving `channelRatio^N ≤ exp(−diagGap g · N^(1−1/g))`.

Every proof placeholder is a requested result.  Minor Mathlib-name adjustments are
fine; keep the mathematical content of each statement.
-/
import RequestProject.RpowCorollaries

open scoped BigOperators

namespace ResidueSlices

/-- The diagonal suppression constant `c_g = (1 − cos(2π/g))/4`. -/
noncomputable def diagGap (g : ℕ) : ℝ := (1 - Real.cos (2 * Real.pi / g)) / 4

theorem diagGap_pos {g : ℕ} (hg : 2 ≤ g) : 0 < diagGap g := by
  exact div_pos ( sub_pos.mpr ( by rw [ ← Real.cos_zero ] ; exact Real.cos_lt_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith [ Real.pi_pos, show 2 * Real.pi / g ≤ Real.pi by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( g : ℝ ) ≥ 2 by norm_cast ] ] ) ( by nlinarith [ Real.pi_pos, show ( g : ℝ ) ≥ 2 by norm_cast, div_mul_cancel₀ ( 2 * Real.pi ) ( by positivity : ( g : ℝ ) ≠ 0 ) ] ) ) ) zero_lt_four

/-
A nontrivial power of a primitive `g`-th root of unity has real part at
most `cos(2π/g)`.
-/
lemma re_pow_le_cos {g : ℕ} (hg : 2 ≤ g) {ω : ℂ} (hω : IsPrimitiveRoot ω g)
    {a : ℕ} (ha : a < g) (ha0 : a ≠ 0) :
    (ω ^ a).re ≤ Real.cos (2 * Real.pi / g) := by
      by_contra h_contra;
      -- Since ω is a primitive root, we can write ω = e^(2πi k/g) for some integer k coprime to g.
      obtain ⟨k, hk⟩ : ∃ k : ℤ, ω = Complex.exp (2 * Real.pi * Complex.I * k / g) ∧ Int.gcd k g = 1 := by
        obtain ⟨k, hk⟩ : ∃ k : ℤ, ω = Complex.exp (2 * Real.pi * Complex.I * k / g) := by
          have h_exp : ∃ θ : ℝ, ω = Complex.exp (θ * Complex.I) := by
            rw [ ← Complex.norm_mul_exp_arg_mul_I ω ];
            exact ⟨ Complex.arg ω, by rw [ show ‖ω‖ = 1 by have := hω.pow_eq_one; have := congr_arg Norm.norm this; norm_num at this; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop ] ; norm_num ⟩;
          obtain ⟨ θ, rfl ⟩ := h_exp; have := hω.pow_eq_one; simp_all +decide [ ← Complex.exp_nat_mul ] ;
          rw [ Complex.exp_eq_one_iff ] at this; obtain ⟨ k, hk ⟩ := this; exact ⟨ k, congr_arg Complex.exp <| by rw [ eq_div_iff ( Nat.cast_ne_zero.mpr <| by linarith ) ] ; linear_combination hk ⟩ ;
        refine' ⟨ k, hk, _ ⟩;
        have := hω.2 ( g / Int.gcd k g ) ?_;
        · exact le_antisymm ( Nat.le_of_not_lt fun h => absurd this ( Nat.not_dvd_of_pos_of_lt ( Nat.div_pos ( Nat.le_of_dvd ( by positivity ) ( Int.natCast_dvd_natCast.mp ( Int.gcd_dvd_right _ _ ) ) ) ( by positivity ) ) ( Nat.div_lt_self ( by positivity ) h ) ) ) ( Nat.gcd_pos_of_pos_right _ ( by positivity ) );
        · rw [ hk, ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff ];
          use k / Int.gcd k g;
          rw [ Int.cast_div ( Int.gcd_dvd_left _ _ ) ] <;> norm_num ; ring;
          · rw [ Nat.cast_div ( Int.natCast_dvd_natCast.mp ( Int.gcd_dvd_right _ _ ) ) ] <;> norm_num ; ring ; norm_num [ show g ≠ 0 by positivity ];
            aesop;
          · aesop;
      -- Since $k$ is coprime to $g$, $a * k$ modulo $g$ gives every residue exactly once. Thus, $ω^a = e^(2πi * ak/g)$ for some integer $ak$.
      have h_exp : ∃ m : ℤ, 0 < m ∧ m < g ∧ ω ^ a = Complex.exp (2 * Real.pi * Complex.I * m / g) := by
        refine' ⟨ a * k % g, _, _, _ ⟩ <;> norm_num [ hk.1, ← Complex.exp_nat_mul ];
        · refine' lt_of_le_of_ne ( Int.emod_nonneg _ ( by positivity ) ) ( Ne.symm _ );
          intro H; have := Int.dvd_of_emod_eq_zero H; simp_all +decide ;
          -- Since $g \mid a * k$ and $\gcd(k, g) = 1$, it follows that $g \mid a$.
          have h_div : (g : ℤ) ∣ a := by
            exact Int.dvd_of_dvd_mul_left_of_gcd_one this ( by simpa [ Int.gcd_comm ] using hk.2 );
          exact absurd h_div ( mod_cast Nat.not_dvd_of_pos_of_lt ( Nat.pos_of_ne_zero ha0 ) ha );
        · exact Int.emod_lt_of_pos _ ( by positivity );
        · rw [ Complex.exp_eq_exp_iff_exists_int ];
          refine' ⟨ a * k / g, _ ⟩ ; push_cast [ Int.emod_def ] ; ring;
          norm_num [ show g ≠ 0 by positivity ];
      obtain ⟨ m, hm₀, hm₁, hm₂ ⟩ := h_exp; simp_all +decide [ Complex.exp_re ] ;
      -- Since $m$ is a positive integer less than $g$, we have $2 * Real.pi * m / g \in [0, 2 * Real.pi)$.
      have h_angle_range : 0 ≤ 2 * Real.pi * m / g ∧ 2 * Real.pi * m / g ≤ Real.pi ∨ Real.pi < 2 * Real.pi * m / g ∧ 2 * Real.pi * m / g < 2 * Real.pi := by
        by_cases h_case : 2 * Real.pi * m / g ≤ Real.pi;
        · exact Or.inl ⟨ by positivity, h_case ⟩;
        · exact Or.inr ⟨ not_le.mp h_case, by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( m : ℝ ) + 1 ≤ g by norm_cast ] ⟩;
      cases' h_angle_range with h_angle_range h_angle_range <;> [ exact h_contra.not_ge ( Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by linarith ) ( by nlinarith [ Real.pi_pos, show ( m :ℝ ) ≥ 1 by exact_mod_cast hm₀, show ( g :ℝ ) ≥ m + 1 by exact_mod_cast hm₁, mul_div_cancel₀ ( 2 * Real.pi * m ) ( by positivity : ( g :ℝ ) ≠ 0 ), mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( g :ℝ ) ≠ 0 ) ] ) ) ; exact h_contra.not_ge ( by rw [ ← Real.cos_two_pi_sub ] ; exact Real.cos_le_cos_of_nonneg_of_le_pi ( by nlinarith [ Real.pi_pos, show ( m :ℝ ) ≥ 1 by exact_mod_cast hm₀, show ( g :ℝ ) ≥ m + 1 by exact_mod_cast hm₁, mul_div_cancel₀ ( 2 * Real.pi * m ) ( by positivity : ( g :ℝ ) ≠ 0 ), mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( g :ℝ ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( m :ℝ ) ≥ 1 by exact_mod_cast hm₀, show ( g :ℝ ) ≥ m + 1 by exact_mod_cast hm₁, mul_div_cancel₀ ( 2 * Real.pi * m ) ( by positivity : ( g :ℝ ) ≠ 0 ), mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( g :ℝ ) ≠ 0 ) ] ) ( by nlinarith [ Real.pi_pos, show ( m :ℝ ) ≥ 1 by exact_mod_cast hm₀, show ( g :ℝ ) ≥ m + 1 by exact_mod_cast hm₁, mul_div_cancel₀ ( 2 * Real.pi * m ) ( by positivity : ( g :ℝ ) ≠ 0 ), mul_div_cancel₀ ( 2 * Real.pi ) ( by positivity : ( g :ℝ ) ≠ 0 ) ] ) ) ] ;

/-
**Pointwise diagonal channel suppression**
(`residue_packetization.tex`, Lemma [Uniform off-axis suppression]):
on the diagonal `1 ≤ n ≤ N`, every subordinate channel ratio at `t = n^(1/g)`
is suppressed at the stretched-exponential rate `exp(−c_g·N^(1−1/g))`.
-/
theorem channelRatio_diagonal_bound
    {g : ℕ} (hg : 2 ≤ g) {ω : ℂ} (hω : IsPrimitiveRoot ω g)
    {a : ℕ} (ha : a < g) (ha0 : a ≠ 0)
    {n N : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    channelRatio ((n : ℝ) ^ ((g : ℝ))⁻¹) ω a ^ N ≤
      Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) := by
        -- Let $t = n^{1/g}$. We have $1 \leq t \leq N^{1/g}$.
        set t : ℝ := (n : ℝ) ^ ((g : ℝ)⁻¹)
        have ht1 : 1 ≤ t := by
          exact Real.one_le_rpow ( mod_cast hn1 ) ( by positivity )
        have htN : t ≤ (N : ℝ) ^ ((g : ℝ)⁻¹) := by
          exact Real.rpow_le_rpow ( by positivity ) ( mod_cast hnN ) ( by positivity )
        -- We have $(channelRatio t ω a)^2 \leq 1 - 2(1 - \cos(2π/g))t/(1+t)^2$.
        have h_sq : (channelRatio t ω a) ^ 2 ≤ 1 - 2 * (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2 := by
          -- We have $‖1 + tω^a‖^2 = (1 + tω^a)(1 + tω^{-a}) = 1 + 2t \Re(ω^a) + t^2$.
          have h_norm_sq : ‖1 + (t : ℂ) * ω ^ a‖ ^ 2 = 1 + 2 * t * (ω ^ a).re + t ^ 2 := by
            norm_num [ Complex.normSq, Complex.sq_norm ];
            -- Since $ω$ is a primitive $g$-th root of unity, we have $|ω^a| = 1$.
            have h_abs : Complex.normSq (ω ^ a) = 1 := by
              simp +decide [ Complex.normSq_eq_norm_sq, hω.norm'_eq_one ( by linarith ) ];
            norm_num [ Complex.normSq ] at h_abs ; nlinarith;
          -- Substitute the bound on $(ω^a).re$ into the expression for $‖1 + tω^a‖^2$.
          have h_norm_sq_bound : ‖1 + (t : ℂ) * ω ^ a‖ ^ 2 ≤ 1 + 2 * t * Real.cos (2 * Real.pi / g) + t ^ 2 := by
            exact h_norm_sq.symm ▸ by nlinarith [ show ( n : ℝ ) ^ ( g : ℝ ) ⁻¹ ≥ 0 by positivity, show ( ω ^ a |> Complex.re ) ≤ Real.cos ( 2 * Real.pi / g ) by exact re_pow_le_cos hg hω ha ha0 ] ;
          unfold channelRatio; rw [ div_pow, div_le_iff₀ ] <;> try positivity;
          rw [ sub_mul, div_mul_cancel₀ ] <;> nlinarith;
        -- We have $ channelRatio t ω a \leq \exp(- (1 - \cos(2π/g))t / (1 + t)^2)$.
        have h_exp : channelRatio t ω a ≤ Real.exp (- (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2) := by
          have h_exp : channelRatio t ω a ^ 2 ≤ Real.exp (-2 * (1 - Real.cos (2 * Real.pi / g)) * t / (1 + t) ^ 2) := by
            refine le_trans h_sq ?_;
            convert Real.add_one_le_exp _ using 1 ; ring;
          convert Real.le_sqrt_of_sq_le h_exp using 1 ; rw [ Real.sqrt_eq_rpow, ← Real.exp_mul ] ; ring;
        -- We have $ t / (1 + t)^2 \geq N^{-1/g} / 4$.
        have h_bound : t / (1 + t) ^ 2 ≥ (N : ℝ) ^ (-(1 : ℝ) / g) / 4 := by
          rw [ neg_div, Real.rpow_neg ( by positivity ) ];
          rw [ ge_iff_le, div_le_div_iff₀ ] <;> norm_num <;> try positivity;
          rw [ inv_mul_eq_div, div_le_iff₀ ] <;> nlinarith [ show ( N : ℝ ) ^ ( ( g : ℝ ) ⁻¹ ) ≥ 1 by exact Real.one_le_rpow ( mod_cast by linarith ) ( by positivity ) ];
        -- We have $ channelRatio t ω a \leq \exp(- (1 - \cos(2π/g))N^{-1/g} / 4)$.
        have h_exp_bound : channelRatio t ω a ≤ Real.exp (- (1 - Real.cos (2 * Real.pi / g)) * (N : ℝ) ^ (-(1 : ℝ) / g) / 4) := by
          refine le_trans h_exp <| Real.exp_le_exp.mpr ?_;
          convert mul_le_mul_of_nonpos_left h_bound ( show ( - ( 1 - Real.cos ( 2 * Real.pi / g ) ) ) ≤ 0 from neg_nonpos_of_nonneg ( sub_nonneg.mpr ( Real.cos_le_one _ ) ) ) using 1 <;> ring;
        refine le_trans ( pow_le_pow_left₀ ( by exact div_nonneg ( norm_nonneg _ ) ( by positivity ) ) h_exp_bound _ ) ?_;
        rw [ ← Real.exp_nat_mul ] ; ring_nf ; norm_num [ diagGap ];
        rw [ show ( 1 - ( g : ℝ ) ⁻¹ ) = - ( g : ℝ ) ⁻¹ + 1 by ring, Real.rpow_add' ] <;> norm_num ; ring_nf ; norm_num;
        linarith [ inv_lt_one_of_one_lt₀ ( by norm_cast : ( 1 : ℝ ) < g ) ]

/-
The spectral gap obeys the same diagonal bound (it is the max of the
channel ratios, together with the inserted `0`).
-/
theorem spectralGap_diagonal_bound
    {g : ℕ} (hg : 2 ≤ g) {ω : ℂ} (hω : IsPrimitiveRoot ω g)
    {n N : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    spectralGap g ((n : ℝ) ^ ((g : ℝ))⁻¹) ω ^ N ≤
      Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) := by
        convert channelRatio_diagonal_bound hg hω _ _ _ _ using 1 <;> norm_num [ hn1, hnN ];
        rotate_left;
        exact Classical.choose ( show ∃ a ∈ Finset.range g \ { 0 }, spectralGap g ( n ^ ( g : ℝ ) ⁻¹ ) ω = channelRatio ( n ^ ( g : ℝ ) ⁻¹ ) ω a from by
                                  have h_max : ∃ a ∈ Finset.range g \ {0}, ∀ b ∈ Finset.range g \ {0}, channelRatio ((n : ℝ) ^ ((g : ℝ))⁻¹) ω b ≤ channelRatio ((n : ℝ) ^ ((g : ℝ))⁻¹) ω a := by
                                    exact Finset.exists_max_image _ _ ⟨ 1, by norm_num; linarith ⟩
                                  generalize_proofs at *; (
                                  obtain ⟨ a, ha₁, ha₂ ⟩ := h_max; use a; simp_all +decide [ spectralGap ] ;
                                  refine' le_antisymm _ _ <;> simp_all +decide [ Finset.max' ];
                                  · exact ⟨ div_nonneg ( norm_nonneg _ ) ( by positivity ), fun x y hy hy' hx => hx ▸ ha₂ y hy hy' ⟩;
                                  · exact Or.inr ⟨ a, ha₁, le_rfl ⟩) )
        all_goals generalize_proofs at *;
        exact Finset.mem_range.mp ( Finset.mem_sdiff.mp ( Classical.choose_spec ‹∃ x ∈ Finset.range g \ { 0 }, spectralGap g ( n ^ ( g : ℝ ) ⁻¹ ) ω = channelRatio ( n ^ ( g : ℝ ) ⁻¹ ) ω x› |>.1 ) |>.1 );
        grind;
        exact n;
        · exact hn1;
        · exact hnN;
        · exact Classical.choose_spec ‹∃ x ∈ Finset.range g \ { 0 }, spectralGap g ( n ^ ( g : ℝ ) ⁻¹ ) ω = channelRatio ( n ^ ( g : ℝ ) ⁻¹ ) ω x› |>.2 ▸ rfl

/-
**Uniform diagonal estimate**: one explicit threshold in `N` works
simultaneously for every `n` on the diagonal `1 ≤ n ≤ N`, with error
`4(g−1)·exp(−c_g·N^(1−1/g))·n^(−k/g)`.  This is the ratio-level content of
the paper's finite diagonal ζ estimate.
-/
theorem diagonal_slice_ratio_bound
    {g k : ℕ} (hg : 2 ≤ g) (hk : k < g) {ω : ℂ} (hω : IsPrimitiveRoot ω g)
    {n N : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N)
    (hthresh : ((g : ℝ) - 1) *
        Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) ≤ 1 / 2) :
    |slice g k N (n : ℝ) / slice g 0 N (n : ℝ) - (n : ℝ) ^ (-(k : ℝ) / (g : ℝ))| ≤
      4 * ((g : ℝ) - 1) *
        Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) *
        (n : ℝ) ^ (-(k : ℝ) / (g : ℝ)) := by
          -- Apply slice_ratio_explicit_rate_rpow to obtain the bound.
          have h_bound : |slice g k N (n : ℝ) / slice g 0 N (n : ℝ) - (n : ℝ) ^ (-(k : ℝ) / (g : ℝ))| ≤
            4 * ((g - 1) * spectralGap g ((n : ℝ) ^ ((g : ℝ))⁻¹) ω ^ N) * (n : ℝ) ^ (-(k : ℝ) / (g : ℝ)) := by
              convert slice_ratio_explicit_rate_rpow ( by linarith : 0 < g ) hk ( by positivity : 0 < ( n : ℝ ) ) hω _ using 1;
              refine le_trans ?_ hthresh;
              exact mul_le_mul_of_nonneg_left ( spectralGap_diagonal_bound ( by linarith ) hω ( by linarith ) ( by linarith ) ) ( sub_nonneg_of_le ( by norm_cast; linarith ) );
          exact h_bound.trans ( mul_le_mul_of_nonneg_right ( by nlinarith [ show ( g : ℝ ) ≥ 2 by norm_cast, spectralGap_diagonal_bound hg hω hn1 hnN ] ) ( by positivity ) )

/-- The diagonal threshold is met for all sufficiently large `N`: combined
with `diagonal_slice_ratio_bound`, this yields the paper's unconditional
"for all sufficiently large `N`" form of the uniform diagonal estimate. -/
theorem diagonal_threshold_eventually {g : ℕ} (hg : 2 ≤ g) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ((g : ℝ) - 1) *
      Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))) ≤ 1 / 2 := by
  have hpos : 0 < diagGap g := diagGap_pos hg
  have hexp : (0 : ℝ) < 1 - (g : ℝ)⁻¹ := by
    have h1 : (1 : ℝ) < g := by exact_mod_cast (by linarith : 1 < g)
    have := inv_lt_one_of_one_lt₀ h1
    linarith
  have h1 : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - (g : ℝ)⁻¹))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto
      (fun N : ℕ => Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hpos))
  have h3 : Filter.Tendsto
      (fun N : ℕ => ((g : ℝ) - 1) *
        Real.exp (-(diagGap g * (N : ℝ) ^ (1 - (g : ℝ)⁻¹))))
      Filter.atTop (nhds 0) := by
    simpa using h2.const_mul ((g : ℝ) - 1)
  exact Filter.eventually_atTop.mp
    (h3.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2))

end ResidueSlices
