# Residue-Slice & Shadow-Calculus Formalization

Machine-checked Lean 4 proofs for the residue-slice (Pascal packetization) and
quadratic-space shadow-calculus research program of Lukas Carroll.

Every theorem in this repository is verified by the Lean kernel, builds with
**zero `sorry`/`admit`**, and depends only on the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — confirmed by the audit file
in `audit/` and enforced in CI.

## Environment (pinned)

| Component | Version |
|---|---|
| Lean | `leanprover/lean4:v4.28.0` |
| Mathlib | tag `v4.28.0` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`) |

## Build and verify

```
lake exe cache get   # fetch Mathlib binary cache
lake build           # build all modules (no sorry, no warnings-as-errors failures)
lake env lean audit/AxiomAudit.lean   # print axiom dependencies of all principal theorems
```

## Theorem ↔ paper map

### `RequestProject/ResidueSlices.lean` — finite algebra and the g = 2 case
| Lean declaration | Paper claim |
|---|---|
| `slice` | The slice polynomial `Q_{r,N}^{(g)}(x)` (residue_packetization.tex) |
| `packet_decomposition` | Packet reconstruction `∑ t^r Q_r(t^g) = (1+t)^N` (over any comm. semiring) |
| `one_le_slice_zero` | Denominator ≥ 1 on the nonnegative axis (pole-freeness) |
| `square_even_odd`, `square_even_odd_reflected` | Direct/reflected even–odd Pascal identities (g = 2) |
| `square_ratio_error` | Exact relative-error identity for the square-root ratio |
| `tendsto_square_ratio` | `Q_1/Q_0 → t⁻¹`, i.e. `x^(−1/2)` after `x = t²` |

### `RequestProject/GeneralResidueConvergence.lean` — general-g convergence
| Lean declaration | Paper claim |
|---|---|
| `primitive_root_power_sum` | Roots-of-unity orthogonality (arbitrary field) |
| `roots_of_unity_filter` | Fourier extraction of a compressed packet |
| `norm_one_add_pos_mul_lt` | Strict spectral dominance of the principal channel |
| `tendsto_general_slice_ratio` | Modular slice-ratio theorem: `Q_k/Q_0 → t^(−k)` (qualitative core) |

### `RequestProject/QuantitativeSpectralGap.lean` — rate (existential constant)
| Lean declaration | Paper claim |
|---|---|
| `spectralGap` | Subordinate channel ratio `ρ_g(x)` |
| `spectralGap_mem_unitInterval` | `0 ≤ ρ < 1` (note: settles the correct range; `ρ = 0` occurs, e.g. g = 2, x = 1) |
| `general_slice_ratio_spectral_rate(_exp)` | Spectral recovery at geometric rate `C·ρ^N`, all N |

### `RequestProject/ExplicitSpectralRate.lean` — rate (explicit constant)
| Lean declaration | Paper claim |
|---|---|
| `packet_principal_deviation` | `|g·t^k·Q_k − (1+t)^N| ≤ (g−1)ρ^N(1+t)^N` |
| `general_slice_ratio_explicit_rate(_exp)` | Explicit ratio inequality: if `(g−1)ρ^N ≤ 1/2` then error `≤ 4(g−1)ρ^N/t^k` (residue_packetization.tex, explicit estimate) |

### `RequestProject/RpowCorollaries.lean` — literal `Real.rpow` forms
| Lean declaration | Paper claim |
|---|---|
| `slice_zero_pos`, `slice_zero_ne_zero` | Explicit denominator-nonvanishing |
| `tendsto_slice_ratio_rpow` | `Q_k(x)/Q_0(x) → x^(−k/g)` for `x > 0`, stated with `rpow` |
| `slice_ratio_explicit_rate_rpow` | `\|ratio − x^(−k/g)\| ≤ 4(g−1)·ρ^N·x^(−k/g)` past the checkable threshold |

### `RequestProject/HeadTailZeta.lean` — head–tail identity and certified ζ(m)
| Lean declaration | Paper claim |
|---|---|
| `head_tail_identity` | Exact head–tail identity `T + E = x^(−m)` (Prop. 1) |
| `partial_sum_decomposition` | Dirichlet partial-sum split |
| `zeta_certified_bounds` | Certified two-sided ζ(m) bound with `1/((m−1)M^(m−1))` tail (Cor. 1) |

### `RequestProject/SpinFactorCrossNorm.lean` — shadow-calculus algebraic core
| Lean declaration | Paper claim |
|---|---|
| `mul`, `conj`, `q` | Spin-factor product, shadow conjugate, generic norm (shadow_spin_factor.tex) |
| `mul_comm`, `one_mul`, `mul_one` | Commutative unital structure |
| `mul_conj` | Generic-norm relation `x ∘ x̄ = (q_B(x), 0)` |
| `cross_norm_identity`, `signed_mul_conj` | **Cross-Norm Identity** (cross_norm_identity_shadow.tex, Prop. 1) |
| `associator_eq` | Closed-form associator = local rotation packet (tree_indexed_shadow.tex) |
| `jordan_identity` | Jordan identity, exported for **arbitrary** bilinear B (no symmetry hypothesis — a strengthening discovered during formalization) |

### `RequestProject/DiagonalZeta.lean` — uniform diagonal suppression
| Lean declaration | Paper claim |
|---|---|
| `diagGap`, `diagGap_pos` | Suppression constant `c_g = (1 − cos(2π/g))/4 > 0` |
| `re_pow_le_cos` | Nontrivial primitive-root powers have `Re ≤ cos(2π/g)` |
| `channelRatio_diagonal_bound` | Uniform off-axis suppression on the diagonal: channel ratio`^N ≤ exp(−c_g·N^(1−1/g))` for `1 ≤ n ≤ N` (residue_packetization.tex, Lemma [diag-suppression]) |
| `spectralGap_diagonal_bound` | The spectral gap obeys the same stretched-exponential bound |
| `diagonal_threshold_eventually` | The diagonal threshold `(g−1)·exp(−c_g·N^(1−1/g)) ≤ ½` holds for all sufficiently large `N` — making the uniform diagonal estimate unconditional in its "eventually" form |
| `diagonal_slice_ratio_bound` | **Uniform diagonal estimate**: one threshold in `N` gives error `≤ 4(g−1)·exp(−c_g·N^(1−1/g))·n^(−k/g)` for every `1 ≤ n ≤ N` simultaneously |

### `RequestProject/ReversedApproximants.lean` — shifted/reversed approximants
| Lean declaration | Paper claim |
|---|---|
| `qIdx`, `epsIdx`, `revA` | Reversal degree `q_N`, endpoint indicator `ε_N`, reversed polynomials `A_N`/`B_N` (residue_slice_rational_approximation.tex) |
| `revA_eq_slice` | Corrected forward-slice relation, `1 ≤ k < g` (Lemma [forward-slice-relation], repaired per audit finding 7.1) |
| `revB_eq_slice` | `k = 0` denominator identity with explicit `ε_N` endpoint correction (nonzero iff `g ∣ N`) |
| `revA_pos` | Strict positivity / pole-freeness of the approximant family on `(0,∞)` |
| `tendsto_reversed_ratio` | Positive-axis convergence `R_N(x;k,g) → x^(k/g)` |

### `RequestProject/RationalZeta.lean` — rational-exponent diagonal ζ
| Lean declaration | Paper claim |
|---|---|
| `sVal`, `mixedKernel`, `diagZeta` | Rational exponent `s = m + k/g`, mixed kernel `𝒯_{s,N}`, diagonal approximant `Z_N(s)` |
| `tendsto_tailTerm` | `T_{m,N}(x) → x^(−m)` for `x > 0` |
| `tendsto_mixedKernel` | `𝒯_{s,N}(x) → x^(−s)` for `x > 0` (pointwise form of Thm. [Uniform approximation]) |
| `tendsto_diagZeta` | **Diagonal approximation to ζ(s)**: `Z_N(s) → ζ(s)` for rational `s > 1` — the composition theorem completing the flagship chain |
| `diagZeta_error_bound` | The three-term error estimate: `N^(1−s)/(s−1) + C·N^(2m−1)·2^(−N) + D·N·exp(−c_g·N^(1−1/g))` for all sufficiently large `N` |
| `real_rpow_tsum_tail_bound`, `headTerm_uniform_bound`, `mixedKernel_diagonal_error` | Supporting estimates: rpow p-series tail; uniform head-term decay; uniform diagonal kernel error |

### `RequestProject/CompactUniform.lean` — compact-uniform convergence
| Lean declaration | Paper claim |
|---|---|
| `exists_uniform_spectralGap` | On compact `K ⊆ (0,∞)`, the subordinate spectral gap is uniformly `< 1` |
| `tendstoUniformlyOn_slice_ratio` | Forward slice ratios `→ x^(−k/g)` **uniformly** on compact `K ⊆ (0,∞)` (Thm. [slice-ratio], uniform clause) |
| `tendstoUniformlyOn_tailTerm` | `T_{m,N}(x) → x^(−m)` uniformly on compact `K ⊆ (0,∞)` |
| `tendstoUniformlyOn_mixedKernel` | `𝒯_{s,N}(x) → x^(−s)` uniformly on compact `K` — the full Thm. [Uniform approximation of rational powers] |
| `tendstoUniformlyOn_reversed_ratio` | Reversed approximants `R_N(x;k,g) → x^(k/g)` uniformly on compact `K` (Thm. [Geometric convergence], uniform clause) |

### `RequestProject/ReversedRate.lean` — combined geometric rate
| Lean declaration | Paper claim |
|---|---|
| `revT`, `combinedRate` | The reversal variable `t = (x⁻¹)^(1/g)` and combined rate `R = max(ρ, t/(1+t))`, `ρ = spectralGap g t (exp 2πi/g)` |
| `combinedRate_mem_unitInterval` | `0 ≤ R < 1` (all boundaries, incl. `g = 1`, `ρ = 0`) |
| `endpointCorrection_geometric_bound` | The corrected `ε_N` endpoint term decays at rate `r = t/(1+t)` |
| `reversed_ratio_geometric_bound` | `\|R_N(x;k,g) − x^(k/g)\| ≤ C·R^N` eventually — the paper's `O(max(ρ, t/(1+t))^N)` combined rate |
| `reversed_ratio_isBigO` | The same, in Mathlib `IsBigO` form at `atTop` |

### `RequestProject/ResidualCertificate.lean` — generator-agnostic certification interface
A standalone module (imports only Mathlib) giving an order-certificate
interface for positive fractional powers `T = x^(−a/g)`, usable by any
generator (binomial slices, Poisson kernels, …) that produces bracketing
values. All statements use natural-power arithmetic only — no `Real.rpow`.
| Lean declaration | Statement |
|---|---|
| `residual_order_lower` / `residual_order_upper` | From `x^a·A^b ≤ 1` (resp. `≥ 1`) and `x^a·T^b = 1`, deduce `A ≤ T` (resp. `T ≤ A`) |
| `residual_bracket` | `x^a·L^b ≤ 1 ≤ x^a·U^b` ⟹ `L ≤ T ≤ U` |
| `residual_pair_intersection` | Two brackets containing `T` intersect to `max Lᵢ ≤ T ≤ min Uᵢ` |
| `residual_finset_intersection` | Nonempty finite family: `s.sup' L ≤ T ≤ s.inf' U` (empty case excluded via `Finset.Nonempty`) |
| `sqrt_ten_certificate` | Worked example: `(79/25)² ≤ 10 ≤ (16/5)²`, hence `79/25 ≤ √10 ≤ 16/5` |

Quantitative relative-error bounds (same module, natural-power / no-calculus):
| Lean declaration | Statement |
|---|---|
| `pow_residual_relative_bound` | `\|r^b − 1\| ≤ η < 1` ⟹ `\|r − 1\| ≤ η / (b(1−η))` (via `r^b−1 = (r−1)·∑_{j<b} r^j`) |
| `fractional_residual_relative_bound` | Generator-facing: residual `\|x^a·A^b − 1\| ≤ η` ⟹ `\|A/T − 1\| ≤ η / (b(1−η))` |
| `residual_positive_enclosure` | Overshoot (`x^a·A^b ≥ 1`): `A/(1+ε) ≤ T ≤ A`, `ε = η/(b(1−η))` |
| `residual_negative_enclosure` | Undershoot (`x^a·A^b ≤ 1`), `ε < 1`: `A ≤ T ≤ A/(1−ε)` (positivity of `1−ε` proved, not assumed) |
| `sqrt_ten_bracket_via_interface` | `31622/10000 ≤ √10 ≤ 31623/10000`, proved *through* `residual_bracket` (`x=1/10, a=1, b=2`) |

### `RequestProject/SlitPlane.lean` — principal-branch (complex) convergence
| Lean declaration | Paper claim |
|---|---|
| `norm_one_add_root_mul_lt` | Complex spectral dominance in the principal sector: `\|arg s\| < π/g`, `s ≠ 0` ⟹ `\|1 + ω^ℓ s\| < \|1 + s\|` for every `ℓ ≠ 0` |
| `tendsto_slice_ratio_cpow` | **Principal-branch convergence on the slit plane**: for `x ∈ ℂ∖(−∞,0]`, `slice g k N x⁻¹ / slice g 0 N x⁻¹ → x^(k/g)` (Thm. [Principal-branch convergence]) |

## Not machine-checked (coverage boundary)

For honesty in both directions: the following paper claims are **not**
certified by any theorem in this repository (boundary confirmed by an
independent statement-fidelity audit, 2026-07-19, and re-checked after the
compact-uniform additions).

- On the slit plane, only the *forward slice ratio* is certified
  (`tendsto_slice_ratio_cpow`, pointwise); the reversed/endpoint `A_N/B_N`
  form over ℂ and *local uniformity* on `ℂ∖(−∞,0]` are not.
- From the rational-approximation paper: Padé identification, monotonicity,
  node-placement/Zolotarev claims, filter acceleration, Veronese interlacing,
  and ray-root pole geometry.
- Spin factor: bilinearity as exported lemmas, full power-associativity,
  conjugation as an involution, the inverse formula, and the downstream
  cross-norm closure and tree-indexed transport theorems.

## Provenance

- Original construction posted publicly: GitHub `vecst/pasNthRoot` (2016-09-06);
  r/math post `co7o64` (2019).
- Aristotle (Harmonic) runs: `4a932f3e`, `8ebd5541`, `078c8fcd`, `d1b648d0`,
  `d5e443bd`, `30895d95`, `566d2ac1` — see `ARISTOTLE_SUMMARY.md`.
  `ExplicitSpectralRate.lean` and `RpowCorollaries.lean` were developed and
  verified locally.
- Independent third-party audit (build, axiom, claim-correspondence) performed
  2026-07-19 on the initial three-module core: claim status *exact*.

## Attribution

Portions of this project were generated by
[Aristotle](https://aristotle.harmonic.fun) (Harmonic).

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
