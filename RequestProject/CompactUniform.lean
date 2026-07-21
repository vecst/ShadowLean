/-
Target statements for Aristotle: compact-uniform convergence on compact
subsets of (0,∞) — the last remaining delta between the papers' stated
theorem forms and the formalized ones
(`residue_packetization.tex` Thm. [slice-ratio] / Thm. [Uniform
approximation of rational powers], uniform clauses;
`residue_slice_rational_approximation.tex` Thm. [Geometric convergence],
uniform clause).

Proof route.  Everything reduces to the compact spectral gap:
`channelRatio t ω a = ‖1 + t·ω^a‖/(1+t)` is continuous in `t`, so
`spectralGap g t ω` (a max over finitely many channels) is continuous in
`t`; composing with the continuous `x ↦ x^(1/g)` on `x > 0` and using
`spectralGap_mem_unitInterval` pointwise, a continuous function `< 1` on a
compact set attains a maximum `ρ_K < 1`.  Then
`slice_ratio_explicit_rate_rpow` gives, once `(g−1)ρ_K^N ≤ 1/2`, the
uniform bound `4(g−1)ρ_K^N · sup_K x^(−k/g)` (finite since `K` is compact
in `(0,∞)`), which tends to `0`.  For `tailTerm`, bound
`headTerm m N x = headPoly/(x^m·slice 2 0 N x)` uniformly on `K ⊆ [a,b]`:
`headPoly m N x ≤ headPoly m N b` (nonnegative coefficients), and
`2·slice 2 0 N (t²) ≥ (1+t)^N(1−ρ^N)` with `t = √x ≥ √a` via
`packet_principal_deviation`.  The mixed kernel is the product of two
uniformly convergent, uniformly bounded sequences.  For the reversed
family, `u = x⁻¹` ranges in a compact subset of `(0,∞)` and the endpoint
term `ε_N u^(q_N+1)` is uniformly dominated by the principal wave as in
`tendsto_reversed_ratio`, now with the compact gap.

Every declaration below is a requested result.  Minor Mathlib-name adjustments are
fine; keep the mathematical content of each statement.
-/
import RequestProject.RationalZeta
import RequestProject.ReversedApproximants

open scoped BigOperators

namespace ResidueSlices

/-
**Compact spectral gap**: on a compact `K ⊆ (0,∞)`, the subordinate
spectral gap is uniformly bounded below one.
-/
theorem exists_uniform_spectralGap {g : ℕ} (hg : 0 < g)
    {ω : ℂ} (hω : IsPrimitiveRoot ω g)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi (0 : ℝ)) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ x ∈ K, spectralGap g (x ^ ((g : ℝ))⁻¹) ω ≤ ρ := by
        -- By definition of spectralGap, it is continuous on the positive reals.
        have h_cont : ContinuousOn (fun t : ℝ => spectralGap g t ω) (Set.Ioi 0) := by
          refine' ContinuousOn.congr _ _;
          exact fun t => Finset.max' ( Finset.image ( fun a => ‖1 + t * ω ^ a‖ / ( 1 + t ) ) ( Finset.range g \ { 0 } ) ∪ { 0 } ) ⟨ 0, by simp +decide ⟩;
          · intro t ht;
            refine' tendsto_order.2 ⟨ _, _ ⟩;
            · intro a' ha';
              simp_all +decide [ Finset.max' ];
              rcases ha' with ( ha' | ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ );
              · exact Or.inl ha';
              · refine' Or.inr _;
                have h_cont : Filter.Tendsto (fun x : ℝ => ‖1 + x * ω ^ a‖ / (1 + x)) (nhdsWithin t (Set.Ioi 0)) (nhds (‖1 + t * ω ^ a‖ / (1 + t))) := by
                  exact Filter.Tendsto.div ( Continuous.continuousWithinAt ( by continuity ) ) ( Continuous.continuousWithinAt ( by continuity ) ) ( by positivity );
                filter_upwards [ h_cont.eventually ( lt_mem_nhds ha₃ ) ] with x hx using ⟨ a, ⟨ ha₁, ha₂ ⟩, hx ⟩;
            · intro a' ha';
              simp_all +decide [ Finset.max' ];
              -- Since $a'$ is positive and the function $f(b) = \frac{\|1 + b \omega^x\|}{1 + b}$ is continuous, there exists a neighborhood around $t$ where $f(b) < a'$.
              have h_cont : ∀ x < g, x ≠ 0 → ∃ ε > 0, ∀ b, abs (b - t) < ε → ‖1 + b * ω ^ x‖ / (1 + b) < a' := by
                intro x hx hx'; have := ha'.2 _ x hx hx' rfl; exact Metric.mem_nhds_iff.mp ( ContinuousAt.preimage_mem_nhds ( show ContinuousAt ( fun b : ℝ => ‖1 + ( b : ℂ ) * ω ^ x‖ / ( 1 + b ) ) t from ContinuousAt.div ( ContinuousAt.norm <| ContinuousAt.add continuousAt_const <| ContinuousAt.mul ( Complex.continuous_ofReal.continuousAt ) <| continuousAt_const ) ( ContinuousAt.add continuousAt_const <| continuousAt_id ) <| by positivity ) <| Iio_mem_nhds this ) ;
              choose! ε hε₁ hε₂ using h_cont;
              -- Choose ε to be the minimum of the ε_x's.
              obtain ⟨ε_min, hε_min⟩ : ∃ ε_min > 0, ∀ x < g, x ≠ 0 → ε_min ≤ ε x := by
                by_cases h_empty : Finset.filter (fun x => x ≠ 0) (Finset.range g) = ∅;
                · rcases g with ( _ | _ | g ) <;> simp_all +decide [ Finset.ext_iff ]; all_goals exact ⟨ 1, by norm_num ⟩;
                · obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ Finset.filter (fun x => x ≠ 0) (Finset.range g), ∀ x ∈ Finset.filter (fun x => x ≠ 0) (Finset.range g), ε x₀ ≤ ε x := by
                    exact Finset.exists_min_image _ _ ( Finset.nonempty_of_ne_empty h_empty );
                  exact ⟨ ε x₀, hε₁ x₀ ( Finset.mem_range.mp ( Finset.mem_filter.mp hx₀.1 |>.1 ) ) ( Finset.mem_filter.mp hx₀.1 |>.2 ), fun x hx₁ hx₂ => hx₀.2 x ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hx₁, hx₂ ⟩ ) ⟩;
              filter_upwards [ self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ( Metric.ball_mem_nhds _ hε_min.1 ) ] with b hb₁ hb₂ using fun a x hx₁ hx₂ hx₃ => hx₃ ▸ hε₂ x hx₁ hx₂ b ( by simpa using hb₂.out.trans_le ( hε_min.2 x hx₁ hx₂ ) );
          · intro t ht; simp +decide [ spectralGap ] ;
            unfold channelRatio; aesop;
        by_cases hK_nonempty : K.Nonempty;
        · obtain ⟨ ρ, hρ ⟩ := IsCompact.exists_isMaxOn hK hK_nonempty ( show ContinuousOn ( fun t : ℝ => spectralGap g ( t ^ ( g : ℝ ) ⁻¹ ) ω ) K from h_cont.comp ( continuousOn_id.rpow_const fun x hx => Or.inr <| by positivity ) fun x hx => Real.rpow_pos_of_pos ( hKpos hx ) _ );
          exact ⟨ _, spectralGap_mem_unitInterval hg ( Real.rpow_pos_of_pos ( hKpos hρ.1 ) _ ) hω |>.1, spectralGap_mem_unitInterval hg ( Real.rpow_pos_of_pos ( hKpos hρ.1 ) _ ) hω |>.2, fun x hx => hρ.2 hx ⟩;
        · exact ⟨ 0, by norm_num, by norm_num, fun x hx => False.elim <| hK_nonempty ⟨ x, hx ⟩ ⟩

/-
**Compact-uniform convergence of the forward slice ratios**
(`residue_packetization.tex`, Thm. [slice-ratio], uniform clause).
-/
theorem tendstoUniformlyOn_slice_ratio {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi (0 : ℝ)) :
    TendstoUniformlyOn (fun N x => slice g k N x / slice g 0 N x)
      (fun x => x ^ (-(k : ℝ) / (g : ℝ))) Filter.atTop K := by
        obtain ⟨ ρ, hρ ⟩ := exists_uniform_spectralGap hg ( Complex.isPrimitiveRoot_exp g hg.ne' ) hK hKpos;
        obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, ((g : ℝ) - 1) * ρ ^ N ≤ 1 / 2 := by
          have h_lim : Filter.Tendsto (fun N => ((g : ℝ) - 1) * ρ ^ N) Filter.atTop (nhds 0) := by
            simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one hρ.1 hρ.2.1 );
          exact Filter.eventually_atTop.mp ( h_lim.eventually ( ge_mem_nhds <| by norm_num ) ) |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, fun N hN x hx => hN₀ N hN ⟩;
        -- By the explicit rate bound, we have |ratio - target| ≤ 4 * ((g - 1) * ρ ^ N) * target for all x ∈ K and N ≥ N₀.
        have h_explicit_rate : ∀ N ≥ N₀, ∀ x ∈ K, |slice g k N x / slice g 0 N x - x ^ (-(k : ℝ) / (g : ℝ))| ≤ 4 * ((g : ℝ) - 1) * ρ ^ N * x ^ (-(k : ℝ) / (g : ℝ)) := by
          intros N hN x hx
          have h_explicit_rate : |slice g k N x / slice g 0 N x - x ^ (-(k : ℝ) / (g : ℝ))| ≤ 4 * ((g : ℝ) - 1) * (spectralGap g (x ^ ((g : ℝ))⁻¹) (Complex.exp (2 * Real.pi * Complex.I / g))) ^ N * x ^ (-(k : ℝ) / (g : ℝ)) := by
            convert slice_ratio_explicit_rate_rpow hg hk ( show 0 < x from hKpos hx ) ( Complex.isPrimitiveRoot_exp g hg.ne' ) _ using 1;
            · ring;
            · exact le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by exact ( spectralGap_mem_unitInterval hg ( show 0 < x ^ ( ( g : ℝ ) ⁻¹ ) from Real.rpow_pos_of_pos ( hKpos hx ) _ ) ( Complex.isPrimitiveRoot_exp g hg.ne' ) ) |>.1 ) ( hρ.2.2 x hx ) _ ) ( sub_nonneg.2 <| Nat.one_le_cast.2 hg ) ) ( hN₀ N hN x hx );
          refine le_trans h_explicit_rate ?_;
          gcongr;
          · exact Real.rpow_nonneg ( le_of_lt ( hKpos hx ) ) _;
          · exact mul_nonneg zero_le_four ( sub_nonneg_of_le ( mod_cast hg ) );
          · exact le_trans ( by norm_num ) ( Finset.le_max' _ _ ( Finset.mem_insert_self _ _ ) );
          · exact hρ.2.2 x hx;
        -- Since $x^{-k/g}$ is continuous and positive on the compact set $K$, it is bounded above by some $B \geq 0$.
        obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x ∈ K, x ^ (-(k : ℝ) / (g : ℝ)) ≤ B := by
          exact ⟨ _, fun x hx => le_csSup ( IsCompact.bddAbove ( hK.image_of_continuousOn ( show ContinuousOn ( fun x : ℝ => x ^ ( - ( k : ℝ ) / g ) ) K from continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| ne_of_gt <| hKpos hx ) ) ) <| Set.mem_image_of_mem _ hx ⟩;
        -- Since $4 * ((g - 1) * ρ ^ N) * B$ tends to $0$ as $N$ tends to infinity, we can conclude the uniform convergence.
        have h_uniform_convergence : Filter.Tendsto (fun N => 4 * ((g : ℝ) - 1) * ρ ^ N * B) Filter.atTop (nhds 0) := by
          simpa using Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one hρ.1 hρ.2.1 ) ) tendsto_const_nhds;
        rw [ Metric.tendstoUniformlyOn_iff ];
        intro ε hε; filter_upwards [ h_uniform_convergence.eventually ( gt_mem_nhds hε ), Filter.eventually_ge_atTop N₀ ] with N hN hN'; intro x hx; rw [ dist_comm ] ; exact lt_of_le_of_lt ( h_explicit_rate N hN' x hx ) ( by nlinarith [ hB x hx, show ( 0 : ℝ ) ≤ 4 * ( g - 1 ) * ρ ^ N by exact mul_nonneg ( mul_nonneg zero_le_four ( sub_nonneg.mpr <| Nat.one_le_cast.mpr hg ) ) <| pow_nonneg hρ.1 _ ] ) ;

/-
The discarded head is antitone on the positive real axis.
-/
lemma headTerm_antitoneOn_Ioi (m N : ℕ) :
    AntitoneOn (headTerm m N) (Set.Ioi (0 : ℝ)) := by
      intro x hx y hy hxy;
      rw [ headTerm, headTerm, div_le_div_iff₀ ];
      · unfold headPoly slice; simp_all +decide [ Finset.sum_mul _ _ _ ] ;
        refine' Finset.sum_le_sum fun i hi => _;
        -- Cancel out the common terms $x^i y^i$ from both sides.
        suffices h_cancel : x ^ (m - i) * (∑ j ∈ Finset.range (N + 1), if j % 2 = 0 then (N.choose j : ℝ) * x ^ (j / 2) else 0) ≤ y ^ (m - i) * (∑ j ∈ Finset.range (N + 1), if j % 2 = 0 then (N.choose j : ℝ) * y ^ (j / 2) else 0) by
          convert mul_le_mul_of_nonneg_left h_cancel ( show 0 ≤ ( N.choose ( 2 * i ) : ℝ ) * x ^ i * y ^ i by positivity ) using 1 <;> ring;
          · rw [ show x ^ m = x ^ i * x ^ ( m - i ) by rw [ ← pow_add, Nat.add_sub_of_le ( Finset.mem_range_le hi ) ] ] ; ring;
          · simp +decide [ mul_assoc, ← pow_add, add_tsub_cancel_of_le ( show i ≤ m from Finset.mem_range_le hi ) ];
        gcongr;
        split_ifs <;> first | positivity | gcongr;
      · exact mul_pos ( pow_pos hy.out _ ) ( slice_zero_pos _ _ hy.out.le );
      · exact mul_pos ( pow_pos hx.out _ ) ( slice_zero_pos _ _ hx.out.le )

/-
**Compact-uniform recovery of integer powers** by the normalized tail
(`residue_packetization.tex`, Thm. [integer recovery], uniform clause).
-/
theorem tendstoUniformlyOn_tailTerm (m : ℕ)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi (0 : ℝ)) :
    TendstoUniformlyOn (fun N x => tailTerm m N x)
      (fun x => (x ^ m)⁻¹) Filter.atTop K := by
        by_cases hK_nonempty : K.Nonempty;
        · have h_headTerm_zero : Filter.Tendsto (fun N => headTerm m N (hK.exists_isLeast hK_nonempty).choose) Filter.atTop (nhds 0) := by
            have h_headTerm_zero : Filter.Tendsto (fun N => tailTerm m N (hK.exists_isLeast hK_nonempty).choose) Filter.atTop (nhds ((hK.exists_isLeast hK_nonempty).choose ^ m)⁻¹) := by
              convert tendsto_tailTerm m ( hKpos ( hK.exists_isLeast hK_nonempty |> Classical.choose_spec |> And.left ) ) using 1;
            convert h_headTerm_zero.const_sub ( ( hK.exists_isLeast hK_nonempty ).choose ^ m ) ⁻¹ using 2 <;> norm_num [ head_tail_identity ];
            rw [ eq_sub_iff_add_eq', head_tail_identity ] ; exact hKpos ( hK.exists_isLeast hK_nonempty |> Classical.choose_spec |> And.left );
          rw [ Metric.tendstoUniformlyOn_iff ];
          intro ε hε_pos
          obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ N ≥ N₀, headTerm m N (hK.exists_isLeast hK_nonempty).choose < ε := by
            simpa using h_headTerm_zero.eventually ( gt_mem_nhds hε_pos );
          filter_upwards [ Filter.eventually_ge_atTop N₀ ] with N hN x hx;
          have h_headTerm_le : headTerm m N x ≤ headTerm m N (hK.exists_isLeast hK_nonempty).choose := by
            apply_rules [ headTerm_antitoneOn_Ioi ];
            · exact hK.exists_isLeast hK_nonempty |>.choose_spec.1;
            · exact Exists.choose_spec ( hK.exists_isLeast hK_nonempty ) |>.2 hx;
          rw [ dist_eq_norm ];
          rw [ Real.norm_eq_abs, abs_of_nonneg ] <;> linarith [ hN₀ N hN, head_tail_identity m N ( hKpos hx ), headTerm_nonneg m N ( hKpos hx ) ];
        · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hK_nonempty, Metric.tendstoUniformlyOn_iff ]

/-
**Compact-uniform convergence of the mixed kernel** — the paper's full
Thm. [Uniform approximation of rational powers].
-/
theorem tendstoUniformlyOn_mixedKernel {m g k : ℕ} (hg : 0 < g) (hk : k < g)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi (0 : ℝ)) :
    TendstoUniformlyOn (fun N x => mixedKernel m g k N x)
      (fun x => x ^ (-sVal m k g)) Filter.atTop K := by
        -- Apply the tendstoUniformlyOn_tailTerm and tendstoUniformlyOn_slice_ratio theorems.
        have h_tail : TendstoUniformlyOn (fun N x => tailTerm m N x) (fun x => (x ^ m)⁻¹) Filter.atTop K := by
          convert tendstoUniformlyOn_tailTerm m hK hKpos using 1
        have h_slice : TendstoUniformlyOn (fun N x => slice g k N x / slice g 0 N x) (fun x => x ^ (-(k : ℝ) / (g : ℝ))) Filter.atTop K := by
          convert tendstoUniformlyOn_slice_ratio hg hk hK hKpos using 1;
        rw [ Metric.tendstoUniformlyOn_iff ] at *;
        intro ε hε
        obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ K, |x ^ (-m : ℝ)| ≤ δ ∧ |x ^ (-(k : ℝ) / (g : ℝ))| ≤ δ := by
          have h_bounded : ContinuousOn (fun x : ℝ => x ^ (-m : ℝ)) K ∧ ContinuousOn (fun x : ℝ => x ^ (-(k : ℝ) / (g : ℝ))) K := by
            exact ⟨ continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| ne_of_gt <| hKpos hx, continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| ne_of_gt <| hKpos hx ⟩;
          obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ > 0, ∀ x ∈ K, |x ^ (-m : ℝ)| ≤ δ₁ := by
            obtain ⟨ δ₁, hδ₁ ⟩ := IsCompact.exists_bound_of_continuousOn hK h_bounded.1; use Max.max δ₁ 1; aesop;
          obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ K, |x ^ (-(k : ℝ) / (g : ℝ))| ≤ δ₂ := by
            obtain ⟨ δ₂, hδ₂ ⟩ := IsCompact.exists_bound_of_continuousOn hK h_bounded.2; use Max.max δ₂ 1; aesop;
          use max δ₁ δ₂;
          exact ⟨ lt_max_of_lt_left hδ₁.1, fun x hx => ⟨ le_trans ( hδ₁.2 x hx ) ( le_max_left _ _ ), le_trans ( hδ₂.2 x hx ) ( le_max_right _ _ ) ⟩ ⟩;
        have h_tail_bound : ∀ᶠ n in Filter.atTop, ∀ x ∈ K, |tailTerm m n x| ≤ δ + 1 := by
          filter_upwards [ h_tail 1 zero_lt_one ] with n hn x hx using abs_le.mpr ⟨ by linarith [ abs_lt.mp ( hn x hx ), abs_le.mp ( hδ x hx |>.1 ), show ( x ^ m : ℝ ) ⁻¹ = x ^ ( -m : ℝ ) by rw [ Real.rpow_neg ( le_of_lt ( hKpos hx ) ) ] ; norm_cast ], by linarith [ abs_lt.mp ( hn x hx ), abs_le.mp ( hδ x hx |>.1 ), show ( x ^ m : ℝ ) ⁻¹ = x ^ ( -m : ℝ ) by rw [ Real.rpow_neg ( le_of_lt ( hKpos hx ) ) ] ; norm_cast ] ⟩;
        filter_upwards [ h_tail ( ε / ( 2 * ( δ + 1 ) ) ) ( by positivity ), h_slice ( ε / ( 2 * ( δ + 1 ) ) ) ( by positivity ), h_tail_bound ] with n hn hn' hn'' x hx;
        have h_dist : |x ^ (-sVal m k g : ℝ) - mixedKernel m g k n x| ≤ |x ^ (-m : ℝ) - tailTerm m n x| * |x ^ (-(k : ℝ) / (g : ℝ))| + |tailTerm m n x| * |x ^ (-(k : ℝ) / (g : ℝ)) - slice g k n x / slice g 0 n x| := by
          have h_dist : x ^ (-sVal m k g : ℝ) = x ^ (-m : ℝ) * x ^ (-(k : ℝ) / (g : ℝ)) := by
            rw [ ← Real.rpow_add ( hKpos hx ) ] ; unfold sVal ; ring;
          rw [ ← abs_mul, ← abs_mul ];
          rw [ h_dist, show mixedKernel m g k n x = tailTerm m n x * ( slice g k n x / slice g 0 n x ) by rfl ] ; rw [ sub_mul, mul_sub ] ; ring_nf;
          exact abs_sub_le _ _ _;
        simp_all +decide [ dist_eq_norm ];
        nlinarith [ hn x hx, hn' x hx, hn'' x hx, hδ x hx, abs_nonneg ( ( x ^ m ) ⁻¹ - tailTerm m n x ), abs_nonneg ( x ^ ( -k / g : ℝ ) - slice g k n x / slice g 0 n x ), mul_div_cancel₀ ε ( by positivity : ( 2 * ( δ + 1 ) ) ≠ 0 ) ]

/-
The endpoint correction in the reversed denominator is uniformly negligible
on compact positive sets.
-/
lemma tendstoUniformlyOn_endpointCorrection {g : ℕ} (hg : 0 < g)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi (0 : ℝ)) :
    TendstoUniformlyOn
      (fun N x => epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N (x⁻¹))
      (fun _ => 0) Filter.atTop K := by
        by_contra h_contra;
        -- Apply the packet_principal_deviation lemma to get the uniform bound.
        obtain ⟨ρ, hρ_nonneg, hρ_lt_one, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ x ∈ K, spectralGap g (x⁻¹ ^ ((g : ℝ))⁻¹) (Complex.exp (2 * Real.pi * Complex.I / g)) ≤ ρ := by
          convert exists_uniform_spectralGap hg ( Complex.isPrimitiveRoot_exp _ _ ) ( hK.image_of_continuousOn ( show ContinuousOn ( fun x : ℝ => x⁻¹ ) K from ContinuousOn.inv₀ continuousOn_id fun x hx => ne_of_gt <| hKpos hx ) ) _ using 1;
          · ext; aesop;
          · positivity;
          · exact Set.image_subset_iff.mpr fun x hx => by simpa using hKpos hx;
        -- Use the fact that $g * slice g 0 N u \geq (1+t)^N / 2$ for sufficiently large $N$.
        have h_bound : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, g * slice g 0 N (x⁻¹) ≥ (1 + x⁻¹ ^ ((g : ℝ))⁻¹) ^ N / 2 := by
          obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, ((g : ℝ) - 1) * spectralGap g (x⁻¹ ^ ((g : ℝ))⁻¹) (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N ≤ 1 / 2 := by
            have h_bound : Filter.Tendsto (fun N => (g - 1) * ρ ^ N) Filter.atTop (nhds 0) := by
              simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nonneg hρ_lt_one );
            exact Filter.eventually_atTop.mp ( h_bound.eventually ( ge_mem_nhds <| by norm_num ) ) |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, fun N hN x hx => le_trans ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by exact ( show 0 ≤ spectralGap g ( x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ( Complex.exp ( 2 * Real.pi * Complex.I / g ) ) from by
                                                                                                                                                                                                                      exact Finset.le_max' _ _ ( Finset.mem_insert_self _ _ ) |> le_trans ( by norm_num ) ) ) ( hρ x hx ) _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr hg ) <| hN₀ N hN ⟩;
          use N₀;
          intros N hN x hx
          have h_bound : |(g : ℝ) * (x⁻¹ ^ ((g : ℝ))⁻¹) ^ 0 * slice g 0 N ((x⁻¹ ^ ((g : ℝ))⁻¹) ^ g) - (1 + x⁻¹ ^ ((g : ℝ))⁻¹) ^ N| ≤ ((g : ℝ) - 1) * spectralGap g (x⁻¹ ^ ((g : ℝ))⁻¹) (Complex.exp (2 * Real.pi * Complex.I / g)) ^ N * (1 + x⁻¹ ^ ((g : ℝ))⁻¹) ^ N := by
            convert packet_principal_deviation hg ( show 0 < g from hg ) ( show 0 < x⁻¹ ^ ( ( g : ℝ ) ⁻¹ ) from Real.rpow_pos_of_pos ( inv_pos.mpr ( hKpos hx ) ) _ ) ( Complex.isPrimitiveRoot_exp _ _ ) N using 1;
            linarith;
          simp_all +decide [ ← Real.rpow_natCast, ← Real.rpow_mul ( inv_nonneg.mpr ( le_of_lt ( hKpos hx ) ) ) ];
          simp_all +decide [ hg.ne' ];
          nlinarith [ abs_le.mp h_bound, hN₀ N hN x hx, show 0 < ( 1 + x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ N by exact pow_pos ( add_pos zero_lt_one ( Real.rpow_pos_of_pos ( inv_pos.mpr ( hKpos hx ) ) _ ) ) _ ];
        -- Use the fact that $u^{q+1} \leq \max(1,t)^g * t^N$ for sufficiently large $N$.
        have h_endpoint_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ N ≥ g, x⁻¹ ^ (qIdx g N + 1) ≤ C * (x⁻¹ ^ ((g : ℝ))⁻¹) ^ N := by
          -- Use the fact that $u^{q+1} \leq \max(1,t)^g * t^N$ for sufficiently large $N$. This follows from the properties of exponents.
          have h_endpoint_bound : ∀ x ∈ K, ∀ N ≥ g, x⁻¹ ^ (qIdx g N + 1) ≤ (max 1 (x⁻¹ ^ ((g : ℝ))⁻¹)) ^ g * (x⁻¹ ^ ((g : ℝ))⁻¹) ^ N := by
            intros x hx N hN
            have h_exp : (qIdx g N + 1 : ℝ) ≤ (N : ℝ) / g + 1 := by
              norm_num [ qIdx ];
              rw [ le_div_iff₀ ] <;> norm_cast ; nlinarith [ Nat.div_mul_le_self ( N - 1 ) g, Nat.sub_add_cancel ( by linarith : 1 ≤ N ) ];
            have h_exp : x⁻¹ ^ (qIdx g N + 1) ≤ (x⁻¹ ^ ((g : ℝ))⁻¹) ^ (g * (qIdx g N + 1)) := by
              rw [ ← Real.rpow_natCast _ ( g * ( qIdx g N + 1 ) ), ← Real.rpow_mul ( inv_nonneg.mpr ( le_of_lt ( hKpos hx ) ) ) ] ; norm_num [ hg.ne' ];
              norm_cast ; norm_num;
            refine le_trans h_exp ?_;
            rw [ show g * ( qIdx g N + 1 ) = N + ( g * ( qIdx g N + 1 ) - N ) by rw [ Nat.add_sub_cancel' ] ; nlinarith [ Nat.div_add_mod ( N - 1 ) g, Nat.mod_lt ( N - 1 ) hg, Nat.sub_add_cancel ( by linarith : 1 ≤ N ), show qIdx g N = ( N - 1 ) / g from rfl ] ] ; ring_nf;
            gcongr;
            · exact pow_nonneg ( Real.rpow_nonneg ( inv_nonneg.2 ( le_of_lt ( hKpos hx ) ) ) _ ) _;
            · refine' le_trans ( pow_le_pow_left₀ _ _ _ ) _;
              exact max 1 ( x⁻¹ ^ ( g : ℝ ) ⁻¹ );
              · exact Real.rpow_nonneg ( inv_nonneg.2 ( le_of_lt ( hKpos hx ) ) ) _;
              · exact le_max_right _ _;
              · refine' pow_le_pow_right₀ _ _;
                · exact le_max_left _ _;
                · rw [ tsub_le_iff_left ] ; nlinarith [ Nat.div_mul_le_self ( N - 1 ) g, Nat.sub_add_cancel ( by linarith : 1 ≤ N ), show qIdx g N = ( N - 1 ) / g from rfl ];
          -- Use the fact that $max(1,t)^g$ is bounded on compact $K$.
          obtain ⟨C, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, max 1 (x⁻¹ ^ ((g : ℝ))⁻¹) ^ g ≤ C := by
            have h_max_bound : ContinuousOn (fun x : ℝ => max 1 (x⁻¹ ^ ((g : ℝ))⁻¹) ^ g) K := by
              exact ContinuousOn.pow ( ContinuousOn.sup continuousOn_const <| ContinuousOn.rpow ( continuousOn_id.inv₀ fun x hx => ne_of_gt <| hKpos hx ) continuousOn_const <| by intro x hx; exact Or.inr <| by positivity ) _;
            obtain ⟨ C, hC ⟩ := IsCompact.exists_bound_of_continuousOn hK h_max_bound;
            exact ⟨ C, le_trans ( abs_nonneg _ ) ( hC _ ( Classical.choose_spec ( Set.nonempty_iff_ne_empty.mpr ( by aesop_cat ) ) ) ), fun x hx => le_of_abs_le ( hC x hx ) ⟩;
          exact ⟨ C, hC.1, fun x hx N hN => le_trans ( h_endpoint_bound x hx N hN ) ( mul_le_mul_of_nonneg_right ( hC.2 x hx ) ( pow_nonneg ( Real.rpow_nonneg ( inv_nonneg.2 ( le_of_lt ( hKpos hx ) ) ) _ ) _ ) ) ⟩;
        -- Use the fact that $t/(1+t)$ is continuous and pointwise in $(0,1)$, so its maximum $r0$ on compact $K$ is $<1$.
        obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, 0 ≤ r0 ∧ r0 < 1 ∧ ∀ x ∈ K, x⁻¹ ^ ((g : ℝ))⁻¹ / (1 + x⁻¹ ^ ((g : ℝ))⁻¹) ≤ r0 := by
          have h_max : ∃ r0 ∈ (Set.image (fun x => x⁻¹ ^ ((g : ℝ))⁻¹ / (1 + x⁻¹ ^ ((g : ℝ))⁻¹)) K), ∀ y ∈ (Set.image (fun x => x⁻¹ ^ ((g : ℝ))⁻¹ / (1 + x⁻¹ ^ ((g : ℝ))⁻¹)) K), y ≤ r0 := by
            apply_rules [ IsCompact.exists_isGreatest, hK.image_of_continuousOn ];
            · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.rpow ( continuousAt_id.inv₀ <| ne_of_gt <| hKpos hx ) continuousAt_const <| Or.inr <| by positivity ) ( ContinuousAt.add continuousAt_const <| ContinuousAt.rpow ( continuousAt_id.inv₀ <| ne_of_gt <| hKpos hx ) continuousAt_const <| Or.inr <| by positivity ) <| by exact ne_of_gt <| add_pos_of_pos_of_nonneg zero_lt_one <| Real.rpow_nonneg ( inv_nonneg.2 <| le_of_lt <| hKpos hx ) _;
            · exact Set.Nonempty.image _ ( Set.nonempty_iff_ne_empty.mpr ( by rintro rfl; exact h_contra <| by simp +decide [ TendstoUniformlyOn ] ) );
          obtain ⟨ r0, hr0₁, hr0₂ ⟩ := h_max; use r0; simp_all +decide [ div_le_iff₀ ] ;
          obtain ⟨ x, hx₁, hx₂ ⟩ := hr0₁; exact ⟨ hx₂ ▸ div_nonneg ( Real.rpow_nonneg ( inv_nonneg.2 ( le_of_lt ( hKpos hx₁ ) ) ) _ ) ( add_nonneg zero_le_one ( Real.rpow_nonneg ( inv_nonneg.2 ( le_of_lt ( hKpos hx₁ ) ) ) _ ) ), hx₂ ▸ by rw [ div_lt_iff₀ ] <;> linarith [ Real.rpow_pos_of_pos ( inv_pos.2 ( hKpos hx₁ ) ) ( ( g : ℝ ) ⁻¹ ) ] ⟩ ;
        -- Use the fact that $g * slice g 0 N u \geq (1+t)^N / 2$ and $u^{q+1} \leq C * t^N$ to bound the expression.
        obtain ⟨N₀, hN₀⟩ := h_bound
        obtain ⟨C, hC_nonneg, hC_bound⟩ := h_endpoint_bound
        have h_final_bound : ∀ N ≥ max N₀ g, ∀ x ∈ K, |epsIdx g N * x⁻¹ ^ (qIdx g N + 1) / slice g 0 N x⁻¹| ≤ 2 * g * C * r0 ^ N := by
          intros N hN x hx
          have h_bound : |epsIdx g N * x⁻¹ ^ (qIdx g N + 1) / slice g 0 N x⁻¹| ≤ 2 * g * x⁻¹ ^ (qIdx g N + 1) / (1 + x⁻¹ ^ ((g : ℝ))⁻¹) ^ N := by
            rw [ abs_of_nonneg ];
            · rw [ div_le_div_iff₀ ];
              · have := hN₀ N ( le_trans ( le_max_left _ _ ) hN ) x hx;
                unfold epsIdx;
                split_ifs <;> nlinarith [ show 0 < x⁻¹ ^ ( qIdx g N + 1 ) by exact pow_pos ( inv_pos.mpr ( hKpos hx ) ) _, show 0 < ( 1 + x⁻¹ ^ ( g : ℝ ) ⁻¹ ) ^ N by exact pow_pos ( add_pos zero_lt_one ( Real.rpow_pos_of_pos ( inv_pos.mpr ( hKpos hx ) ) _ ) ) _ ];
              · exact slice_zero_pos _ _ ( inv_nonneg.mpr ( le_of_lt ( hKpos hx ) ) );
              · exact pow_pos ( add_pos zero_lt_one ( Real.rpow_pos_of_pos ( inv_pos.mpr ( hKpos hx ) ) _ ) ) _;
            · exact div_nonneg ( mul_nonneg ( by unfold epsIdx; split_ifs <;> norm_num ) ( pow_nonneg ( inv_nonneg.2 ( le_of_lt ( hKpos hx ) ) ) _ ) ) ( slice_nonneg _ _ _ ( inv_nonneg.2 ( le_of_lt ( hKpos hx ) ) ) );
          refine le_trans h_bound ?_;
          rw [ div_le_iff₀ ( pow_pos ( add_pos zero_lt_one ( Real.rpow_pos_of_pos ( inv_pos.mpr ( hKpos hx ) ) _ ) ) _ ) ];
          refine le_trans ( mul_le_mul_of_nonneg_left ( hC_bound x hx N ( by linarith [ Nat.le_max_right N₀ g ] ) ) ( by positivity ) ) ?_;
          rw [ mul_assoc, mul_assoc ];
          rw [ ← mul_pow ];
          rw [ mul_assoc, mul_assoc ];
          exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( by exact Real.rpow_nonneg ( inv_nonneg.mpr ( le_of_lt ( hKpos hx ) ) ) _ ) ( by have := hr0.2.2 x hx; rw [ div_le_iff₀ ( by exact add_pos zero_lt_one ( Real.rpow_pos_of_pos ( inv_pos.mpr ( hKpos hx ) ) _ ) ) ] at this; linarith ) _ ) hC_nonneg ) ( Nat.cast_nonneg _ ) ) zero_le_two;
        -- Use the fact that $r0 < 1$ to show that $2 * g * C * r0 ^ N$ tends to $0$ as $N$ tends to infinity.
        have h_tendsto_zero : Filter.Tendsto (fun N => 2 * g * C * r0 ^ N) Filter.atTop (nhds 0) := by
          simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one hr0.1 hr0.2.1 );
        refine' h_contra _;
        rw [ Metric.tendstoUniformlyOn_iff ];
        intro ε hε; filter_upwards [ h_tendsto_zero.eventually ( gt_mem_nhds hε ), Filter.eventually_ge_atTop ( max N₀ g ) ] with N hN₁ hN₂; intro x hx; simpa [ abs_div, abs_mul ] using lt_of_le_of_lt ( h_final_bound N hN₂ x hx ) hN₁;

/-
**Compact-uniform convergence of the reversed approximants**
(`residue_slice_rational_approximation.tex`, Thm. [Geometric convergence],
uniform clause).
-/
theorem tendstoUniformlyOn_reversed_ratio {g k : ℕ} (hg : 0 < g) (hk : k < g)
    {K : Set ℝ} (hK : IsCompact K) (hKpos : K ⊆ Set.Ioi (0 : ℝ)) :
    TendstoUniformlyOn (fun N x => revA g k N x / revA g 0 N x)
      (fun x => x ^ ((k : ℝ) / (g : ℝ))) Filter.atTop K := by
        by_cases hk0 : k = 0 <;> simp_all +decide [ div_eq_mul_inv ];
        · rw [ Metric.tendstoUniformlyOn_iff ];
          intro ε hε; filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN; intro x hx; rw [ mul_inv_cancel₀ ] <;> norm_num [ hε ] ;
          exact ne_of_gt ( revA_pos ( by linarith ) ( hKpos hx ) );
        · have h_revA_eq : ∀ᶠ N in Filter.atTop, ∀ x ∈ K, revA g k N x = x ^ qIdx g N * slice g k N x⁻¹ ∧ revA g 0 N x = x ^ qIdx g N * (slice g 0 N x⁻¹ - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1)) := by
            filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN x hx;
            exact ⟨ revA_eq_slice hg ( Nat.pos_of_ne_zero hk0 ) hk ( hKpos hx ), revB_eq_slice hg hN ( hKpos hx ) ⟩;
          have h_revA_eq : ∀ᶠ N in Filter.atTop, ∀ x ∈ K, revA g k N x / revA g 0 N x = (slice g k N x⁻¹ / slice g 0 N x⁻¹) / (1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N x⁻¹) := by
            filter_upwards [ h_revA_eq, Filter.eventually_gt_atTop 0 ] with N hN hN' x hx ; rw [ hN x hx |>.1, hN x hx |>.2 ] ; rw [ mul_div_mul_left _ _ ( pow_ne_zero _ <| ne_of_gt <| hKpos hx ) ] ; rw [ sub_div' ] ; ring ;
            · by_cases h : slice g 0 N x⁻¹ = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
              · exact absurd h ( ne_of_gt ( slice_zero_pos _ _ ( inv_nonneg.mpr ( le_of_lt ( hKpos hx ) ) ) ) );
              · field_simp [h];
                norm_num;
            · exact ne_of_gt <| slice_zero_pos _ _ <| inv_nonneg.2 <| le_of_lt <| hKpos hx;
          have h_revA_eq : TendstoUniformlyOn (fun N x => slice g k N x⁻¹ / slice g 0 N x⁻¹) (fun x => x⁻¹ ^ (-(k : ℝ) / (g : ℝ))) Filter.atTop K := by
            have h_revA_eq : TendstoUniformlyOn (fun N x => slice g k N x / slice g 0 N x) (fun x => x ^ (-(k : ℝ) / (g : ℝ))) Filter.atTop (Set.image (fun x => x⁻¹) K) := by
              apply_rules [ tendstoUniformlyOn_slice_ratio ];
              · exact hK.image_of_continuousOn ( continuousOn_id.inv₀ fun x hx => ne_of_gt <| hKpos hx );
              · exact Set.image_subset_iff.mpr fun x hx => by simpa using hKpos hx;
            exact fun ε hε => by filter_upwards [ h_revA_eq ε hε ] with N hN x hx using hN _ <| Set.mem_image_of_mem _ hx;
          have h_revA_eq : TendstoUniformlyOn (fun N x => epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N x⁻¹) (fun x => 0) Filter.atTop K := by
            have := @ResidueSlices.tendstoUniformlyOn_endpointCorrection;
            exact this hg hK hKpos;
          have h_revA_eq : TendstoUniformlyOn (fun N x => (slice g k N x⁻¹ / slice g 0 N x⁻¹) / (1 - epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N x⁻¹)) (fun x => x⁻¹ ^ (-(k : ℝ) / (g : ℝ)) / (1 - 0)) Filter.atTop K := by
            rw [ Metric.tendstoUniformlyOn_iff ] at *;
            intro ε hε
            obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ K, |x⁻¹ ^ (-(k : ℝ) / (g : ℝ))| ≤ δ := by
              have h_revA_eq : ContinuousOn (fun x : ℝ => x⁻¹ ^ (-(k : ℝ) / (g : ℝ))) K := by
                exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow ( continuousAt_id.inv₀ <| ne_of_gt <| hKpos hx ) continuousAt_const <| Or.inl <| ne_of_gt <| inv_pos.mpr <| hKpos hx;
              obtain ⟨ δ, hδ ⟩ := IsCompact.exists_bound_of_continuousOn hK h_revA_eq; use Max.max δ 1; aesop;
            obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ N ≥ N₀, ∀ x ∈ K, |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N x⁻¹| < 1 / 2 := by
              exact Filter.eventually_atTop.mp ( h_revA_eq ( 1 / 2 ) ( by norm_num ) ) |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, fun N hN x hx => by simpa [ abs_div, abs_mul ] using hN₀ N hN x hx ⟩;
            obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ N ≥ N₁, ∀ x ∈ K, |x⁻¹ ^ (-(k : ℝ) / (g : ℝ)) - slice g k N x⁻¹ / slice g 0 N x⁻¹| < ε / (2 * (δ + 1)) := by
              exact Filter.eventually_atTop.mp ( ‹∀ ε > 0, ∀ᶠ n in Filter.atTop, ∀ x ∈ K, dist ( x⁻¹ ^ ( -k / g : ℝ ) ) ( slice g k n x⁻¹ / slice g 0 n x⁻¹ ) < ε› ( ε / ( 2 * ( δ + 1 ) ) ) ( by positivity ) ) |> fun ⟨ N₁, hN₁ ⟩ => ⟨ N₁, fun N hN x hx => hN₁ N hN x hx ⟩;
            obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ N ≥ N₂, ∀ x ∈ K, |epsIdx g N * (x⁻¹) ^ (qIdx g N + 1) / slice g 0 N x⁻¹| < ε / (2 * (δ + 1)) := by
              exact Filter.eventually_atTop.mp ( h_revA_eq ( ε / ( 2 * ( δ + 1 ) ) ) ( by positivity ) ) |> fun ⟨ N₂, hN₂ ⟩ => ⟨ N₂, fun N hN x hx => by simpa [ abs_div, abs_mul ] using hN₂ N hN x hx ⟩;
            filter_upwards [ Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop N₁, Filter.eventually_ge_atTop N₂ ] with N hN₀ hN₁ hN₂ x hx;
            simp_all +decide [ abs_lt, dist_eq_norm ];
            rename_i h₁ h₂ h₃;
            constructor <;> nlinarith [ h₁ N hN₀ x hx, h₂ N hN₁ x hx, h₃ N hN₂ x hx, abs_le.mp ( hδ x hx ), mul_div_cancel₀ ( ε : ℝ ) ( by positivity : ( 2 * ( δ + 1 ) ) ≠ 0 ), mul_div_cancel₀ ( slice g k N x⁻¹ / slice g 0 N x⁻¹ ) ( by linarith [ h₁ N hN₀ x hx ] : ( 1 - epsIdx g N * ( x ^ ( qIdx g N + 1 ) ) ⁻¹ / slice g 0 N x⁻¹ ) ≠ 0 ) ];
          simp_all +decide [ div_eq_mul_inv, Real.rpow_neg_eq_inv_rpow ];
          intro ε hε; rcases ‹∃ a, ∀ b : ℕ, a ≤ b → ∀ x ∈ K, revA g k b x = x ^ qIdx g b * slice g k b x⁻¹ ∧ revA g 0 b x = x ^ qIdx g b * ( slice g 0 b x⁻¹ - epsIdx g b * ( x ^ ( qIdx g b + 1 ) ) ⁻¹ ) › with ⟨ a, ha ⟩ ; rcases ‹∃ a, ∀ b : ℕ, a ≤ b → ∀ x ∈ K, revA g k b x * ( revA g 0 b x ) ⁻¹ = slice g k b x⁻¹ * ( slice g 0 b x⁻¹ ) ⁻¹ * ( 1 - epsIdx g b * ( x ^ ( qIdx g b + 1 ) ) ⁻¹ * ( slice g 0 b x⁻¹ ) ⁻¹ ) ⁻¹ › with ⟨ b, hb ⟩ ; filter_upwards [ h_revA_eq ε hε, Filter.Ici_mem_atTop a, Filter.Ici_mem_atTop b ] with n hn hn' hn'' using fun x hx => by simpa only [ hb n hn'' x hx ] using hn x hx;

end ResidueSlices