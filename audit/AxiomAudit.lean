/-
Axiom audit for all 330 public theorem/lemma declarations. Run with:
  lake env lean audit/AxiomAudit.lean
Every dependency list must be a subset of
[propext, Classical.choice, Quot.sound]. Public definitions are covered by the
strict build and complete declaration inventory rather than duplicated here.
-/
import RequestProject.Main

-- ResidueSlices core
#print axioms ResidueSlices.packet_decomposition
#print axioms ResidueSlices.one_le_slice_zero
#print axioms ResidueSlices.square_ratio_error
#print axioms ResidueSlices.tendsto_square_ratio

-- General-g convergence
#print axioms ResidueSlices.roots_of_unity_filter
#print axioms ResidueSlices.tendsto_general_slice_ratio

-- Quantitative rate
#print axioms ResidueSlices.spectralGap_mem_unitInterval
#print axioms ResidueSlices.general_slice_ratio_spectral_rate
#print axioms ResidueSlices.general_slice_ratio_spectral_rate_exp

-- Explicit rate
#print axioms ResidueSlices.packet_principal_deviation
#print axioms ResidueSlices.general_slice_ratio_explicit_rate
#print axioms ResidueSlices.general_slice_ratio_explicit_rate_exp

-- rpow corollaries
#print axioms ResidueSlices.slice_zero_pos
#print axioms ResidueSlices.slice_zero_ne_zero
#print axioms ResidueSlices.tendsto_slice_ratio_rpow
#print axioms ResidueSlices.slice_ratio_explicit_rate_rpow

-- Head–tail and certified ζ
#print axioms ResidueSlices.head_tail_identity
#print axioms ResidueSlices.partial_sum_decomposition
#print axioms ResidueSlices.zeta_certified_bounds

-- Diagonal suppression and uniform diagonal estimate
#print axioms ResidueSlices.diagGap_pos
#print axioms ResidueSlices.re_pow_le_cos
#print axioms ResidueSlices.channelRatio_diagonal_bound
#print axioms ResidueSlices.spectralGap_diagonal_bound
#print axioms ResidueSlices.diagonal_slice_ratio_bound
#print axioms ResidueSlices.diagonal_threshold_eventually

-- Reversed approximants (corrected endpoint treatment)
#print axioms ResidueSlices.revA_eq_slice
#print axioms ResidueSlices.revB_eq_slice
#print axioms ResidueSlices.revA_pos
#print axioms ResidueSlices.tendsto_reversed_ratio

-- Rational-exponent diagonal zeta
#print axioms ResidueSlices.tendsto_tailTerm
#print axioms ResidueSlices.tendsto_mixedKernel
#print axioms ResidueSlices.tendsto_diagZeta
#print axioms ResidueSlices.diagZeta_error_bound
#print axioms ResidueSlices.real_rpow_tsum_tail_bound
#print axioms ResidueSlices.headTerm_uniform_bound
#print axioms ResidueSlices.mixedKernel_diagonal_error

-- Compact-uniform convergence
#print axioms ResidueSlices.exists_uniform_spectralGap
#print axioms ResidueSlices.tendstoUniformlyOn_slice_ratio
#print axioms ResidueSlices.tendstoUniformlyOn_tailTerm
#print axioms ResidueSlices.tendstoUniformlyOn_mixedKernel
#print axioms ResidueSlices.tendstoUniformlyOn_reversed_ratio

-- Reversed-approximant combined rate
#print axioms ResidueSlices.combinedRate_mem_unitInterval
#print axioms ResidueSlices.endpointCorrection_geometric_bound
#print axioms ResidueSlices.reversed_ratio_geometric_bound
#print axioms ResidueSlices.reversed_ratio_isBigO

-- Slit-plane (principal-branch complex) convergence
#print axioms ResidueSlices.norm_one_add_root_mul_lt
#print axioms ResidueSlices.tendsto_slice_ratio_cpow

-- Reversed approximant over the slit plane (Targets 1-7 active)
#print axioms ResidueSlices.revAComplex_eq_slice
#print axioms ResidueSlices.revBComplex_eq_slice
#print axioms ResidueSlices.tendsto_endpointCorrection_cpow
#print axioms ResidueSlices.tendsto_reversed_ratio_cpow
#print axioms ResidueSlices.tendstoUniformlyOn_slice_ratio_cpow
#print axioms ResidueSlices.tendstoUniformlyOn_endpointCorrection_cpow
#print axioms ResidueSlices.tendstoUniformlyOn_reversed_ratio_cpow

-- Residual certificate interface (generator-agnostic)
#print axioms ResidualCertificate.residual_order_lower
#print axioms ResidualCertificate.residual_order_upper
#print axioms ResidualCertificate.residual_bracket
#print axioms ResidualCertificate.residual_pair_intersection
#print axioms ResidualCertificate.residual_finset_intersection
#print axioms ResidualCertificate.sqrt_ten_certificate
#print axioms ResidualCertificate.pow_residual_relative_bound
#print axioms ResidualCertificate.fractional_residual_relative_bound
#print axioms ResidualCertificate.residual_positive_enclosure
#print axioms ResidualCertificate.residual_negative_enclosure
#print axioms ResidualCertificate.sqrt_ten_bracket_via_interface

-- Packet derivative jet (Fourier core and Targets 7-9 Stirling moments active)
#print axioms ResidueSlices.forwardDiff_binomial_symbol
#print axioms ResidueSlices.forwardDiffSymbol_eq_pow
#print axioms ResidueSlices.forwardDiffPacket_eq_dft_sum
#print axioms ResidueSlices.forwardDiffSymbol_zero
#print axioms ResidueSlices.forwardDiffPacket_eq_dft_sum_erase_zero
#print axioms ResidueSlices.forwardDiffPacket_movingPacketMass
#print axioms ResidueSlices.forwardDiff_moment_eq_factorial_mul_stirlingSecond
#print axioms ResidueSlices.forwardDiff_moment_vanish
#print axioms ResidueSlices.forwardDiff_top_moment

-- Packet high-pass (moving-packet Fourier identity + total-variation bound)
#print axioms ResidueSlices.dft_movingPacketMass
#print axioms ResidueSlices.movingPacketMass_add_one_sub
#print axioms ResidueSlices.stdAddChar_sub_one_mul_dft
#print axioms ResidueSlices.dft_norm_mul_le_cyclicVariation
#print axioms ResidueSlices.movingPacket_dft_highpass_bound

-- Packet high-pass, divided (nonzero-frequency bounds)
#print axioms ResidueSlices.stdAddChar_sub_one_norm_pos
#print axioms ResidueSlices.dft_norm_le_cyclicVariation_div
#print axioms ResidueSlices.movingPacket_dft_divided_bound

-- IFFT-prepared spectral support under packet flow
#print axioms ResidueSlices.packetSpectralFlow_zero
#print axioms ResidueSlices.packetSpectralFlow_succ
#print axioms ResidueSlices.packetSpectralFlow_zero_of_initial_zero
#print axioms ResidueSlices.packetSpectralFlow_supported
#print axioms ResidueSlices.packetSpectrum_evolvedPreparedPacket
#print axioms ResidueSlices.packetSpectrum_evolvedPreparedPacket_succ
#print axioms ResidueSlices.evolvedPreparedPacket_no_spectral_leakage

-- IFFT coordinate-recurrence <-> spectral-flow bridge (one-step equivalence)
#print axioms ResidueSlices.preparedPacket_packetSpectrum
#print axioms ResidueSlices.packetSpectrum_injective
#print axioms ResidueSlices.packetCoordinateStep_zero
#print axioms ResidueSlices.packetCoordinateStep_ne_zero
#print axioms ResidueSlices.packetSpectrum_packetCoordinateStep
#print axioms ResidueSlices.evolvedPreparedPacket_succ_eq_packetCoordinateStep

-- IFFT finite-time iterated coordinate flow (n-step diagonalization + semigroup/support)
#print axioms ResidueSlices.packetSpectrum_packetCoordinateStep_iterate
#print axioms ResidueSlices.evolvedPreparedPacket_zero
#print axioms ResidueSlices.evolvedPreparedPacket_eq_packetCoordinateStep_iterate
#print axioms ResidueSlices.packetCoordinateStep_iterate_evolvedPreparedPacket
#print axioms ResidueSlices.packetCoordinateStep_iterate_no_spectral_leakage
#print axioms ResidueSlices.packetSpectrum_packetCoordinateStep_iterate_eq_zero_iff
#print axioms ResidueSlices.packetCoordinateStep_iterate_support_eq

-- IFFT preparation (exact finite-g spectral reconstruction)
#print axioms ResidueSlices.preparedScaledPacket_formula
#print axioms ResidueSlices.positiveDFT_preparedScaledPacket
#print axioms ResidueSlices.packetSpectrum_preparedPacket
#print axioms ResidueSlices.preparedPacket_no_spectral_leakage
#print axioms ResidueSlices.preparedPacket_conj_eq_self
#print axioms ResidueSlices.preparedPacket_pos_of_dominant_zero

-- Dual-slice logarithm (powers -> log via two-stage limit)
#print axioms ResidueSlices.tendsto_binomialLog_row
#print axioms ResidueSlices.logSurrogate_eq_tanh
#print axioms ResidueSlices.tendsto_logSurrogate
#print axioms ResidueSlices.binomialLog_iterated_converges_to_log
#print axioms ResidueSlices.tendstoUniformlyOn_binomialLog_row

-- Metallic-cutoff recurrence (Targets 1-4 proved; 5-8 open)
#print axioms MetallicCutoff.state_neg_one_even
#print axioms MetallicCutoff.state_neg_one_odd
#print axioms MetallicCutoff.silver_identities
#print axioms MetallicCutoff.ratio_three_closed_form
#print axioms MetallicCutoff.even_pole_residue

-- Spin factor / cross-norm
#print axioms SpinFactor.mul_comm
#print axioms SpinFactor.mul_conj
#print axioms SpinFactor.cross_norm_identity
#print axioms SpinFactor.signed_mul_conj
#print axioms SpinFactor.associator_eq
#print axioms SpinFactor.mul_self_assoc
#print axioms SpinFactor.jordan_identity

-- Public proof helpers omitted by the former principal-theorem selection.
-- Keeping them explicit makes this driver a 330/330 public-proof audit.
#print axioms ResidueSlices.unique_residue_packet
#print axioms ResidueSlices.slice_nonneg
#print axioms ResidueSlices.square_even_odd
#print axioms ResidueSlices.square_even_odd_reflected
#print axioms ResidueSlices.square_ratio_cross_error
#print axioms ResidueSlices.two_mul_square_even
#print axioms ResidueSlices.primitive_root_power_sum
#print axioms ResidueSlices.tendsto_finite_mode_sum_zero
#print axioms ResidueSlices.primitive_root_pow_ne_one
#print axioms ResidueSlices.norm_one_add_pos_mul_lt
#print axioms ResidueSlices.tendsto_general_slice_ratio_of_dominance
#print axioms ResidueSlices.tendsto_general_slice_ratio_with_primitive
#print axioms ResidueSlices.channelRatio_le_spectralGap
#print axioms ResidueSlices.slice_ofReal
#print axioms ResidueSlices.headPoly_nonneg
#print axioms ResidueSlices.headPoly_le_slice
#print axioms ResidueSlices.tailTerm_nonneg
#print axioms ResidueSlices.headTerm_nonneg
#print axioms SpinFactor.one_mul
#print axioms SpinFactor.mul_one
#print axioms ResidueSlices.headTerm_antitoneOn_Ioi
#print axioms ResidueSlices.tendstoUniformlyOn_endpointCorrection
#print axioms ResidueSlices.reversedRatioComplex_zero
#print axioms ResidueSlices.exists_uniform_complexSpectralGap
#print axioms ResidueSlices.sliceZero_uniform_lower
#print axioms ResidueSlices.endpointNumerator_uniform_bound
#print axioms ResidueSlices.endpointRatio_uniform_lt_one
#print axioms ResidueSlices.endpointCorrection_uniform_geom_bound
#print axioms MetallicCutoff.state_succ
#print axioms MetallicCutoff.state_neg_one_pair
#print axioms ResidueSlices.forwardDiffCoeff_succ_mul_index
#print axioms ResidueSlices.forwardDiff_moment_zero
#print axioms ResidueSlices.forwardDiff_moment_succ_shift
#print axioms ResidueSlices.forwardDiff_moment_shift_eq_add
#print axioms ResidueSlices.forwardDiff_moment_succ_recurrence

-- Silver-ratio crossover algebra (cubic residual jet + normalized quadratic roots)
#print axioms SilverCrossover.cubicResidual_add_displacement
#print axioms SilverCrossover.cubicResidual_neutral
#print axioms SilverCrossover.cubicResidual_neutral_hasDerivAt
#print axioms SilverCrossover.crossoverScale_sq
#print axioms SilverCrossover.quadraticCrossover_rescale_pos
#print axioms SilverCrossover.quadraticCrossover_rescale_neg
#print axioms SilverCrossover.complex_sq_sqrt
#print axioms SilverCrossover.normalizedRootPlus_isRoot
#print axioms SilverCrossover.normalizedRootMinus_isRoot
#print axioms SilverCrossover.negative_discriminant_of_abs_lt_two
#print axioms SilverCrossover.negative_discriminant_eq_zero_of_abs_eq_two
#print axioms SilverCrossover.positive_discriminant_of_two_lt_abs
#print axioms SilverCrossover.positive_error_discriminant

-- Silver finite-row bridge (generic algebra <-> reversed g=3 Pascal-row packet)
#print axioms SilverFiniteRow.affineInput_center
#print axioms SilverFiniteRow.affineInput_silver
#print axioms SilverFiniteRow.silverConstantFromRadical_isRoot
#print axioms SilverFiniteRow.packetRatio_den_pos
#print axioms SilverFiniteRow.tendsto_finiteMap
#print axioms SilverFiniteRow.finiteMap_center_sub_eq_centerError
#print axioms SilverFiniteRow.tendsto_centerError
#print axioms SilverFiniteRow.tendstoUniformlyOn_finiteMap
#print axioms SilverFiniteRow.cubicResidual_eq_packetDeviation_factor_of_fixed
#print axioms SilverFiniteRow.cubic_displacement_eq_packetDeviation_factor_of_fixed

-- Silver finite-row quantitative remainder layer (crossover eq + envelope bounds + uniform)
#print axioms SilverFiniteRow.quadraticCrossover_eq_centerRemainder_of_fixed
#print axioms SilverFiniteRow.centerRemainder_decomposition
#print axioms SilverFiniteRow.fixedPointFactor_eq_of_fixed
#print axioms SilverFiniteRow.fixedPointFactor_sub_bound
#print axioms SilverFiniteRow.fixedPointFactor_abs_bound
#print axioms SilverFiniteRow.centerRemainder_abs_bound
#print axioms SilverFiniteRow.normalized_positive_crossover_equation
#print axioms SilverFiniteRow.normalized_negative_crossover_equation
#print axioms SilverFiniteRow.tendstoUniformlyOn_packetDeviation
#print axioms SilverFiniteRow.tendstoUniformlyOn_deviationVariation

-- Silver finite-row fixed-point existence (the collapse is real, via IVT on [0,N])
#print axioms SilverFiniteRow.choose_succ_le_nat_mul
#print axioms SilverFiniteRow.continuous_revA
#print axioms SilverFiniteRow.revA_one_le_nat_mul_revA_zero
#print axioms SilverFiniteRow.packetRatio_le_nat
#print axioms SilverFiniteRow.packetRatio_pos
#print axioms SilverFiniteRow.continuousOn_finiteMap_silver
#print axioms SilverFiniteRow.exists_finiteRow_fixedPoint

-- Silver finite-row uniqueness: elasticity/Wronskian machinery + unique fixed point + limiting collapse = alpha
#print axioms SilverFiniteRow.choose_step_mul_le
#print axioms SilverFiniteRow.choose_pair_le
#print axioms SilverFiniteRow.rowCoeff_nonneg
#print axioms SilverFiniteRow.rowPoly_coeff
#print axioms SilverFiniteRow.rowPoly_eval
#print axioms SilverFiniteRow.coeff_rowPoly_mul
#print axioms SilverFiniteRow.coeff_derivative_rowPoly_mul
#print axioms SilverFiniteRow.coeff_rowPoly_mul_derivative
#print axioms SilverFiniteRow.rowCoeff_of_le
#print axioms SilverFiniteRow.rowCoeff_of_gt
#print axioms SilverFiniteRow.rowCoeff_cross_le
#print axioms SilverFiniteRow.rowCoeff_shift_le
#print axioms SilverFiniteRow.pair_term_wronskian_nonneg
#print axioms SilverFiniteRow.pair_term_elasticity_nonpos
#print axioms SilverFiniteRow.antidiag_wronskian_nonneg
#print axioms SilverFiniteRow.antidiag_elasticity_nonpos
#print axioms SilverFiniteRow.coeff_rowWronskian
#print axioms SilverFiniteRow.coeff_rowWronskian_nonneg
#print axioms SilverFiniteRow.coeff_rowElasticity_nonpos
#print axioms SilverFiniteRow.eval_rowWronskian_nonneg
#print axioms SilverFiniteRow.rowCoeff_zero_pos
#print axioms SilverFiniteRow.eval_rowElasticity_neg
#print axioms SilverFiniteRow.eval_wronskian_mul_lt
#print axioms SilverFiniteRow.hasDerivAt_scaledRatio
#print axioms SilverFiniteRow.strictAntiOn_scaledRatio
#print axioms SilverFiniteRow.unique_finiteRow_fixedPoint
#print axioms SilverFiniteRow.limitingMap_fixedPoint_eq

-- Circle-hyperbola: the g=2 gudermannian anchor (mod-2 Pascal slice = tanh of the rapidity)
#print axioms SliceHyperbolic.binomEven_closed
#print axioms SliceHyperbolic.binomOdd_closed
#print axioms SliceHyperbolic.binomSlice_ratio_tanh

-- Circle-hyperbola ladder, general g: character product (normalization) + zeroth multisection
#print axioms SliceHyperbolic.char_product
#print axioms SliceHyperbolic.zeroth_multisection

-- Circle-hyperbola ladder: the full roots-of-unity multisection filter (every residue k)
#print axioms SliceHyperbolic.multisection_filter

-- gd_3 as a named special function: bridge derivatives, circular-image closed forms, autonomous ODE
#print axioms SliceHyperbolic.gd3Psi_hasDerivAt
#print axioms SliceHyperbolic.gd3S_hasDerivAt
#print axioms SliceHyperbolic.gd3_cos
#print axioms SliceHyperbolic.gd3_sin
#print axioms SliceHyperbolic.gd3_ode

-- gd_4 as a named special function: the last single-cotangent rung (dpsi/ds = 2 cot 2psi)
#print axioms SliceHyperbolic.gd4Psi_hasDerivAt
#print axioms SliceHyperbolic.gd4S_hasDerivAt
#print axioms SliceHyperbolic.gd4_cos
#print axioms SliceHyperbolic.gd4_sin
#print axioms SliceHyperbolic.gd4_ode

-- gd_g critical tetranomial: derivative and repeated-root quadratic reduction
#print axioms GdgSquarefree.criticalTetranomial_hasDerivAt
#print axioms GdgSquarefree.criticalTetranomial_common_root_quadratic
#print axioms GdgSquarefree.criticalTetranomial_common_root_reciprocal
#print axioms GdgSquarefree.coverDerivativeNumerator_eq_criticalTetranomial

-- gd_g squarefreeness, analytic candidate-location layer (a_g = 2 cos(2 pi / g))
#print axioms GdgSquarefree.gdgCosCoeff_pos
#print axioms GdgSquarefree.gdgCandidateB_add_two
#print axioms GdgSquarefree.gdgCandidateB_eq_common_root_reciprocal
#print axioms GdgSquarefree.gdgCandidateB_lt_neg_two
#print axioms GdgSquarefree.gdgCandidateB_mem_Ioo_neg_two_zero
#print axioms GdgSquarefree.gdgCandidateB_not_tetranomial_root

-- gd_g critical-value separation: real-variable denominator-gap foundation
#print axioms GdgSquarefree.gdg_scalar_gap_pos
#print axioms GdgSquarefree.gdg_cosh_sub_cos_pos
#print axioms GdgSquarefree.gdg_one_lt_ratio
#print axioms GdgSquarefree.gdg_one_lt_exterior
#print axioms GdgSquarefree.gdg_one_lt_powered

-- gd_g lobe translation: translation dominance of the interior magnitude
#print axioms GdgSquarefree.gdgTheta_pos
#print axioms GdgSquarefree.gdgTheta_lt_pi_div_two
#print axioms GdgSquarefree.gdgInteriorNumeratorAbs_shift
#print axioms GdgSquarefree.gdgInteriorDenominator_shift_pos_lt
#print axioms GdgSquarefree.gdgInteriorMagnitude_shift_lt
#print axioms GdgSquarefree.gdgInteriorMagnitude_max_shift_lt
#print axioms GdgSquarefree.gdgExteriorCriticalRatio_strictAntiOn
#print axioms GdgSquarefree.gdgExteriorCriticalRatio_eq_cos_unique
#print axioms GdgSquarefree.gdgInteriorMagnitude_max_shift_lt_of_pos

-- gd_g natural lobes: zero-to-zero lobe geometry and positive-maximum existence
#print axioms GdgSquarefree.gdgLobeLeft_succ
#print axioms GdgSquarefree.gdgLobeRight_eq_next_left
#print axioms GdgSquarefree.gdgEvenLobe_numerator_values
#print axioms GdgSquarefree.gdgOddLobe_numerator_values
#print axioms GdgSquarefree.gdgInteriorDenominator_pos_on_Icc
#print axioms GdgSquarefree.continuousOn_gdgInteriorMagnitude_of_before_pole
#print axioms GdgSquarefree.exists_gdgInteriorMagnitude_isGreatest_pos
#print axioms GdgSquarefree.exists_pos_even_lobe_max
#print axioms GdgSquarefree.exists_pos_odd_lobe_max

-- gd_g retained lobes (Phase 2A): finite index set, exact counts, pole guard, positive maxima
#print axioms GdgSquarefree.gdg_mem_retainedLobeIndices_iff
#print axioms GdgSquarefree.gdg_card_retainedLobeIndices
#print axioms GdgSquarefree.gdgRetainedLobeCount_eq_even
#print axioms GdgSquarefree.gdgRetainedLobeCount_eq_odd
#print axioms GdgSquarefree.gdgRetainedLobeCount_add_one
#print axioms GdgSquarefree.gdgLobeRight_even_lt_pole_iff
#print axioms GdgSquarefree.gdgLobeRight_odd_lt_pole_iff
#print axioms GdgSquarefree.gdgLobeRight_even_last_lt_pole
#print axioms GdgSquarefree.gdgLobeRight_odd_last_lt_pole
#print axioms GdgSquarefree.exists_pos_even_retained_lobe_max
#print axioms GdgSquarefree.exists_pos_odd_retained_lobe_max

-- gd_g retained lobes (Phase 2A completion): membership iffs, shifted pole guards, disjoint interiors, small-g counts
#print axioms GdgSquarefree.gdgEven_mem_iff_lobeRight_lt_pole
#print axioms GdgSquarefree.gdgOdd_mem_iff_lobeRight_lt_pole
#print axioms GdgSquarefree.gdgEven_next_lobe_before_pole
#print axioms GdgSquarefree.gdgOdd_next_lobe_before_pole
#print axioms GdgSquarefree.gdgLobe_interiors_disjoint_of_lt
#print axioms GdgSquarefree.gdgRetainedLobeCount_five
#print axioms GdgSquarefree.gdgRetainedLobeCount_six
#print axioms GdgSquarefree.gdgRetainedLobeCount_seven

-- gd_g zero classification (Phase 2B): global Int-index + finite pre-pole endpoint + no hidden zeros
#print axioms GdgSquarefree.gdg_mem_retainedZeroIndices_iff
#print axioms GdgSquarefree.gdg_card_retainedZeroIndices
#print axioms GdgSquarefree.gdg_mem_retainedLobeIndices_iff_endpoint_pair
#print axioms GdgSquarefree.gdgEven_numerator_zero_iff_int_index
#print axioms GdgSquarefree.gdgOdd_numerator_zero_iff_int_index
#print axioms GdgSquarefree.gdgEven_numerator_zero_iff_existsUnique_retained_endpoint
#print axioms GdgSquarefree.gdgOdd_numerator_zero_iff_existsUnique_retained_endpoint
#print axioms GdgSquarefree.gdgEven_numerator_pos_on_lobeInterior
#print axioms GdgSquarefree.gdgOdd_numerator_pos_on_lobeInterior

-- gd_g signed lobes (Phase 3A): signed pullback regularity, parity signs, per-lobe Rolle witness
#print axioms GdgSquarefree.abs_gdgSignedInterior_eq_gdgInteriorMagnitude
#print axioms GdgSquarefree.gdgSignedInterior_eq_neg_magnitude_of_even
#print axioms GdgSquarefree.gdgSignedInterior_eq_magnitude_of_odd
#print axioms GdgSquarefree.continuousOn_gdgSignedInterior_of_before_pole
#print axioms GdgSquarefree.differentiableAt_gdgSignedInterior_of_denominator_ne_zero
#print axioms GdgSquarefree.gdgSignedInterior_even_endpoint_values
#print axioms GdgSquarefree.gdgSignedInterior_odd_endpoint_values
#print axioms GdgSquarefree.gdgSignedInterior_neg_on_even_retained_lobeInterior
#print axioms GdgSquarefree.gdgSignedInterior_pos_on_odd_retained_lobeInterior
#print axioms GdgSquarefree.exists_even_retained_lobe_hasDerivAt_gdgSignedInterior_zero
#print axioms GdgSquarefree.exists_odd_retained_lobe_hasDerivAt_gdgSignedInterior_zero

-- gd_g critical bridge (Phase 3B): pulled cover on the unit circle -> located criticalTetranomial roots
#print axioms GdgSquarefree.gdgUnitCircle_ne_zero
#print axioms GdgSquarefree.gdgUnitCircle_add_inv_eq_blockCoord
#print axioms GdgSquarefree.coverQuadratic_gdgUnitCircle
#print axioms GdgSquarefree.coverNumerator_sq_gdgUnitCircle
#print axioms GdgSquarefree.gdgPulledCover_gdgUnitCircle_eq_signed
#print axioms GdgSquarefree.gdgPulledCover_hasDerivAt
#print axioms GdgSquarefree.gdgBlockCoord_hasDerivAt
#print axioms GdgSquarefree.gdgBlockCoord_deriv_ne_zero_on_prePole
#print axioms GdgSquarefree.criticalTetranomial_gdgUnitCircle_eq_zero_of_stationary
#print axioms GdgSquarefree.exists_even_retained_lobe_criticalTetranomial_unitCircle_root
#print axioms GdgSquarefree.exists_odd_retained_lobe_criticalTetranomial_unitCircle_root

-- gd_g critical no-common-root (Phase 4A): tetranomial and its derivative share no root (g>=5)
#print axioms GdgSquarefree.gdgCriticalTetranomial_at_zero
#print axioms GdgSquarefree.gdgCriticalTetranomial_root_ne_zero
#print axioms GdgSquarefree.gdgCriticalTetranomial_deriv_ne_zero_of_root
#print axioms GdgSquarefree.gdgCriticalTetranomial_no_common_root

-- gd_g critical polynomial (Phase 4B): Polynomial realization, exact degree, separability, squarefree (g>=5)
#print axioms GdgSquarefree.gdgCriticalPolynomial_eval
#print axioms GdgSquarefree.gdgCriticalPolynomial_derivative_eval
#print axioms GdgSquarefree.gdgQuadraticPolynomial_eval
#print axioms GdgSquarefree.gdgCriticalPolynomial_natDegree
#print axioms GdgSquarefree.gdgQuadraticPolynomial_monic
#print axioms GdgSquarefree.gdgQuadraticPolynomial_natDegree
#print axioms GdgSquarefree.gdgCriticalPolynomial_ne_zero
#print axioms GdgSquarefree.gdgCriticalPolynomial_derivative_eval_ne_zero_of_root
#print axioms GdgSquarefree.gdgCriticalPolynomial_separable
#print axioms GdgSquarefree.gdgCriticalPolynomial_squarefree

-- gd_g forced quadratic (Phase 4C): exact forced factor Q | P, monic quotient P/ₘQ deg g-2, squarefree factors, coprime (g>=5)
#print axioms GdgSquarefree.gdgQuadraticPolynomial_dvd_critical
#print axioms GdgSquarefree.gdgQuadratic_mul_channelQuotient
#print axioms GdgSquarefree.gdgChannelQuotientPolynomial_natDegree
#print axioms GdgSquarefree.gdgChannelQuotientPolynomial_ne_zero
#print axioms GdgSquarefree.gdgQuadraticPolynomial_squarefree
#print axioms GdgSquarefree.gdgChannelQuotientPolynomial_squarefree
#print axioms GdgSquarefree.gdgQuadratic_channelQuotient_isCoprime
#print axioms GdgSquarefree.gdgCriticalPolynomial_eval_factorization
#print axioms GdgSquarefree.gdgChannelQuotient_eval_eq_zero_iff

-- gd_g reciprocal residual (Phase 4D): odd u=1 removal, parity-correct self-reciprocal squarefree residual, no fixed reciprocal roots (g>=5)
#print axioms GdgSquarefree.gdgChannelQuotient_eval_one_of_odd
#print axioms GdgSquarefree.gdgChannelQuotient_eval_one_of_even
#print axioms GdgSquarefree.gdgChannelQuotient_eval_neg_one
#print axioms GdgSquarefree.gdgXSubOne_mul_oddResidual
#print axioms GdgSquarefree.gdgOddResidualPolynomial_natDegree
#print axioms GdgSquarefree.gdgChannelQuotientPolynomial_reverse
#print axioms GdgSquarefree.gdgOddResidualPolynomial_reverse
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_natDegree
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_reverse
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_squarefree
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_eval_one_ne_zero
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_eval_neg_one_ne_zero

-- gd_g block descent (Phase 4E): reciprocal basis + constructive block polynomial B_g deg (g-2)/2, exact descent R(u)=u^d B(u+u^-1) (g>=5)
#print axioms GdgSquarefree.gdgReciprocalBasis_eval
#print axioms GdgSquarefree.gdgReciprocalBasis_natDegree
#print axioms GdgSquarefree.gdgReciprocalBasis_monic
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_ne_zero
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_coeff_zero_ne_zero
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_root_ne_zero
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_coeff_blockDegree
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_natDegree
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_ne_zero
#print axioms GdgSquarefree.gdgReciprocalResidual_eval_eq_block
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_eval_eq_zero_iff
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_root_of_residual_root

-- gd_g block root bridge (Phase 4F): retained-lobe witnesses -> injective family of block roots (g>=5)
#print axioms GdgSquarefree.gdgUnitCircle_ne_one_of_blockCoord_lt_two
#print axioms GdgSquarefree.gdgChannelQuotientPolynomial_gdgUnitCircle_eq_zero
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_even
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_gdgUnitCircle_eq_zero_of_odd
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_gdgUnitCircle_eq_zero
#print axioms GdgSquarefree.gdgBlockCoord_strictAntiOn
#print axioms GdgSquarefree.gdgBlockCoord_ne_of_lt
#print axioms GdgSquarefree.exists_even_retained_lobe_blockCriticalPolynomial_root
#print axioms GdgSquarefree.exists_odd_retained_lobe_blockCriticalPolynomial_root
#print axioms GdgSquarefree.gdgBlockCoord_ne_of_even_retained_lobes
#print axioms GdgSquarefree.gdgBlockCoord_ne_of_odd_retained_lobes
#print axioms GdgSquarefree.exists_even_retained_lobe_blockRoot_embedding
#print axioms GdgSquarefree.exists_odd_retained_lobe_blockRoot_embedding

-- gd_g exterior root (Phase 5): unique exterior critical point, unique block root b<-2, positive cover value (g>=5)
#print axioms GdgSquarefree.gdgExteriorCriticalRatio_continuous
#print axioms GdgSquarefree.gdgExteriorCriticalRatio_zero
#print axioms GdgSquarefree.tendsto_gdgExteriorCriticalRatio_atTop
#print axioms GdgSquarefree.exists_gdgExteriorCriticalRatio_eq_cos
#print axioms GdgSquarefree.existsUnique_gdgExteriorCriticalRatio_eq_cos
#print axioms GdgSquarefree.gdgExteriorUnit_ne_zero
#print axioms GdgSquarefree.gdgExteriorUnit_ne_one
#print axioms GdgSquarefree.gdgExteriorUnit_add_inv
#print axioms GdgSquarefree.gdgExteriorBlockCoord_lt_neg_two
#print axioms GdgSquarefree.criticalTetranomial_gdgExteriorUnit_eq_zero_iff
#print axioms GdgSquarefree.coverQuadratic_gdgExteriorUnit_ne_zero
#print axioms GdgSquarefree.gdgReciprocalResidualPolynomial_exterior_eq_zero_iff
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_exterior_eq_zero_iff
#print axioms GdgSquarefree.existsUnique_exterior_parametrized_blockRoot
#print axioms GdgSquarefree.existsUnique_exterior_blockRoot
#print axioms GdgSquarefree.gdgPulledCover_gdgExteriorUnit
#print axioms GdgSquarefree.gdgExteriorCoverValue_pos

-- gd_g degree exhaustion (Phase 6A): d_g distinct complex roots exhausted, all roots real (g>=5)
#print axioms GdgSquarefree.card_gdgBlockRootSlot
#print axioms GdgSquarefree.exists_retained_lobe_blockRoot_embedding
#print axioms GdgSquarefree.exists_gdgBlockRootSlot_embedding
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_root_set_finite
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_root_set_ncard
#print axioms GdgSquarefree.exists_gdgBlockRootSlot_classification
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_all_roots_real

-- gd_g lobe uniqueness (Phase 6B): exactly one stationary phase per retained lobe = unique positive magnitude maximizer (g>=5)
#print axioms GdgSquarefree.even_retained_lobe_stationary_blockRoot
#print axioms GdgSquarefree.odd_retained_lobe_stationary_blockRoot
#print axioms GdgSquarefree.exists_even_complete_retained_lobe_blockRoot_family
#print axioms GdgSquarefree.exists_odd_complete_retained_lobe_blockRoot_family
#print axioms GdgSquarefree.existsUnique_even_retained_lobe_stationary
#print axioms GdgSquarefree.existsUnique_odd_retained_lobe_stationary
#print axioms GdgSquarefree.even_retained_lobe_stationary_iff_isGreatest
#print axioms GdgSquarefree.odd_retained_lobe_stationary_iff_isGreatest
#print axioms GdgSquarefree.existsUnique_even_retained_lobe_magnitude_maximizer
#print axioms GdgSquarefree.existsUnique_odd_retained_lobe_magnitude_maximizer

-- gd_g critical value ordering (Phase 7A): strict consecutive retained-lobe value ordering, parity-correct (g>=5)
#print axioms GdgSquarefree.even_retained_lobe_stationary_isGreatest_pos
#print axioms GdgSquarefree.odd_retained_lobe_stationary_isGreatest_pos
#print axioms GdgSquarefree.even_consecutive_retained_stationary_magnitude_lt
#print axioms GdgSquarefree.odd_consecutive_retained_stationary_magnitude_lt
#print axioms GdgSquarefree.even_consecutive_retained_stationary_value_gt
#print axioms GdgSquarefree.odd_consecutive_retained_stationary_value_lt

-- gd_g critical value pairwise (Phase 7B): pairwise j<k ordering + distinct-lobe value noncollision (g>=5)
#print axioms GdgSquarefree.even_pairwise_retained_stationary_magnitude_lt
#print axioms GdgSquarefree.odd_pairwise_retained_stationary_magnitude_lt
#print axioms GdgSquarefree.even_pairwise_retained_stationary_value_gt
#print axioms GdgSquarefree.odd_pairwise_retained_stationary_value_lt
#print axioms GdgSquarefree.even_distinct_retained_stationary_values_ne
#print axioms GdgSquarefree.odd_distinct_retained_stationary_values_ne

-- gd_g exterior value maximum (Phase 8A): exterior critical param = global maximizer of cover value on t>0 (g>=5)
#print axioms GdgSquarefree.gdgExteriorCoverValue_hasDerivAt
#print axioms GdgSquarefree.gdgExterior_logSlope_pos_of_lt_critical
#print axioms GdgSquarefree.gdgExterior_logSlope_neg_of_critical_lt
#print axioms GdgSquarefree.gdgExteriorCoverValue_isGreatest_of_critical
#print axioms GdgSquarefree.gdgExteriorCoverValue_theta_le_of_critical

-- gd_g exterior/interior odd (Phase 8B): odd-row exterior critical value strictly above every retained interior magnitude (g>=7)
#print axioms GdgSquarefree.gdgOdd_retained_lobeRight_le_pi_sub_two_theta
#print axioms GdgSquarefree.gdgOdd_retained_interior_denominator_lower_bound
#print axioms GdgSquarefree.gdgOdd_retained_interior_magnitude_le
#print axioms GdgSquarefree.gdgExteriorCoverValue_at_theta
#print axioms GdgSquarefree.gdg_uniformInteriorBound_lt_exterior_theta
#print axioms GdgSquarefree.gdgOdd_retained_lobe_magnitude_lt_exterior_critical

-- gd_g exterior/interior noncollision (Phase 8C): parity-specific interior stationary value != exterior critical value (g>=5)
#print axioms GdgSquarefree.gdgRetainedLobeIndices_five_eq_empty
#print axioms GdgSquarefree.even_retained_stationary_value_lt_exterior_critical
#print axioms GdgSquarefree.odd_retained_stationary_value_lt_exterior_critical
#print axioms GdgSquarefree.even_retained_stationary_value_ne_exterior_critical
#print axioms GdgSquarefree.odd_retained_stationary_value_ne_exterior_critical

-- gd_g flagship critical family (Phase 9): publication-facing certificate, roots simple/squarefree, exists for every g>=5
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_roots_nodup
#print axioms GdgSquarefree.gdgBlockCriticalPolynomial_squarefree
#print axioms GdgSquarefree.nonempty_even_gdgCriticalFamilyCertificate
#print axioms GdgSquarefree.nonempty_odd_gdgCriticalFamilyCertificate
#print axioms GdgSquarefree.nonempty_gdgCriticalFamilyCertificate

-- IFFT sublattice projector (Phase 1A): divisor-sublattice averaging projector on ZMod g (d | g)
#print axioms ResidueSlices.divisor_pos_of_dvd
#print axioms ResidueSlices.divisor_quotient_pos
#print axioms ResidueSlices.mem_divisorSublattice_iff
#print axioms ResidueSlices.card_divisorSublattice
#print axioms ResidueSlices.sublatticeProjector_normalization
#print axioms ResidueSlices.sublatticeProjector_apply
#print axioms ResidueSlices.positiveDFT_sublatticeProjector_of_mem
#print axioms ResidueSlices.positiveDFT_sublatticeProjector_of_not_mem
#print axioms ResidueSlices.sublatticeProjector_idempotent
#print axioms ResidueSlices.positiveDFT_sublatticeProjector_supported

-- IFFT sublattice convolution closure (Phase 1B): finite convolution support closure on ZMod g
#print axioms ResidueSlices.cyclicConvolution_supported
#print axioms ResidueSlices.cyclicConvolutionPow_supported
#print axioms ResidueSlices.finiteConvolutionSeries_supported
#print axioms ResidueSlices.truncatedLogSpectrum_supported
#print axioms ResidueSlices.truncatedLogSpectrum_projected_supported

-- Executable diagonal logarithm (Phase 2A): explicit surrogate-bias bound
#print axioms ResidueSlices.abs_sub_tanh_le_cube
#print axioms ResidueSlices.logSurrogate_error_bound
#print axioms ResidueSlices.logIntervalBound_nonneg
#print axioms ResidueSlices.abs_log_le_logIntervalBound
#print axioms ResidueSlices.logSurrogate_error_bound_Icc
#print axioms ResidueSlices.one_le_logSurrogateBiasModulus
#print axioms ResidueSlices.logSurrogate_error_lt_of_biasModulus

-- Executable diagonal logarithm (Phase 2B): explicit finite-row rate
#print axioms ResidueSlices.logRowGap_mem_unitInterval
#print axioms ResidueSlices.binomialLog_row_explicit_rate
#print axioms ResidueSlices.binomialLog_row_interval_rate_of_gap_bound
#print axioms ResidueSlices.binomialLog_row_error_lt_of_qualified

-- Executable diagonal logarithm (Phase 2C1): explicit interval spectral-gap envelope
#print axioms ResidueSlices.logRowGapEnvelope_pos
#print axioms ResidueSlices.logRowGapEnvelope_lt_one
#print axioms ResidueSlices.channelRatio_le_logRowGapEnvelope
#print axioms ResidueSlices.logRowGap_le_logRowGapEnvelope
#print axioms ResidueSlices.logRowGapEnvelope_mem_unitInterval
#print axioms ResidueSlices.binomialLog_row_interval_rate
#print axioms ResidueSlices.binomialLog_row_error_lt_of_envelope_qualified

-- Diagonal logarithm (Phase 2C2): explicit row selector and final certified evaluator
#print axioms ResidueSlices.logRowPowerTarget_pos
#print axioms ResidueSlices.logRowPowerTarget_lt_one
#print axioms ResidueSlices.one_le_logRowModulus
#print axioms ResidueSlices.logRowGapEnvelope_pow_logRowModulus_le_target
#print axioms ResidueSlices.logRowQualified_logRowModulus
#print axioms ResidueSlices.two_le_diagonalLogG
#print axioms ResidueSlices.biasModulus_le_diagonalLogG
#print axioms ResidueSlices.diagonalBinomialLog_error_lt

-- Analytic derivative bridge (Phase A3A): unwrapped scaled stencil + no-wrap packet bridge
#print axioms ResidueSlices.forwardDiffPacket_realSamplePacket_eq
#print axioms ResidueSlices.unwrappedForwardDiff_centeredMonomial_vanish
#print axioms ResidueSlices.unwrappedForwardDiff_centeredMonomial_top
#print axioms ResidueSlices.normalizedForwardDiff_centeredMonomial_vanish
#print axioms ResidueSlices.normalizedForwardDiff_centeredMonomial_top
#print axioms ResidueSlices.unwrappedForwardDiff_centeredJetPolynomial
#print axioms ResidueSlices.normalizedForwardDiff_centeredJetPolynomial

-- Analytic derivative bridge (Phase A3B): explicit nodewise Taylor-remainder certificate
#print axioms ResidueSlices.forwardDiffRemainderWeight_nonneg
#print axioms ResidueSlices.unwrappedForwardDiff_sub_jet_eq_remainder_sum
#print axioms ResidueSlices.unwrappedForwardDiff_error_le
#print axioms ResidueSlices.normalizedForwardDiff_sub_jet_eq_div
#print axioms ResidueSlices.normalizedForwardDiff_error_le

-- Analytic derivative bridge (Phase A3C): Taylor certificate, derivative error, packet convergence
#print axioms ResidueSlices.factorial_mul_derivativeJet
#print axioms ResidueSlices.centeredJetPolynomial_derivativeJet_eq_taylor
#print axioms ResidueSlices.hasCenteredJetRemainderAtNodes_derivativeJet
#print axioms ResidueSlices.normalizedForwardDiff_iteratedDeriv_error_le
#print axioms ResidueSlices.tendsto_normalizedForwardDiff_iteratedDeriv
#print axioms ResidueSlices.normalizedForwardDiffPacket_eq
#print axioms ResidueSlices.normalizedForwardDiffPacket_iteratedDeriv_error_le
#print axioms ResidueSlices.tendsto_normalizedForwardDiffPacket_iteratedDeriv

-- Correlated derivative remainder (Phase A3D1): exact next Taylor term + O(h^2) certificate
#print axioms ResidueSlices.forwardDiffSecondRemainderWeight_nonneg
#print axioms ResidueSlices.unwrappedForwardDiff_centeredMonomial_succ
#print axioms ResidueSlices.unwrappedForwardDiff_centeredJetPolynomial_succ
#print axioms ResidueSlices.normalizedForwardDiff_centeredJetPolynomial_succ
#print axioms ResidueSlices.unwrappedForwardDiff_sub_secondJet_eq_remainder_sum
#print axioms ResidueSlices.unwrappedForwardDiff_second_error_le
#print axioms ResidueSlices.normalizedForwardDiff_sub_secondJet_eq_div
#print axioms ResidueSlices.normalizedForwardDiff_second_error_le

-- Correlated derivative remainder (Phase A3D2): r/2 analytic coefficient + scaled packet limit
#print axioms ResidueSlices.factorial_choose_mul_derivativeJet_succ
#print axioms ResidueSlices.hasCenteredJetSecondRemainderAtNodes_derivativeJet
#print axioms ResidueSlices.normalizedForwardDiff_iteratedDeriv_second_error_le
#print axioms ResidueSlices.tendsto_scaled_normalizedForwardDiff_error
#print axioms ResidueSlices.normalizedForwardDiffPacket_iteratedDeriv_second_error_le
#print axioms ResidueSlices.tendsto_scaled_normalizedForwardDiffPacket_error

-- Metallic cutoff Phase B: corrected signed moving-pole law (Target 5)
#print axioms MetallicCutoff.tendsto_even_moving_pole_signed
#print axioms MetallicCutoff.tendsto_even_moving_pole

-- Metallic cutoff Phase C1: canonical even-row recovery fixed point (Target 6)
#print axioms MetallicCutoff.recoveryMap
#print axioms MetallicCutoff.scaledRecoveryRatio
#print axioms MetallicCutoff.evenFixedPoint
#print axioms MetallicCutoff.recovery_denominator_pos
#print axioms MetallicCutoff.continuousOn_recoveryMap
#print axioms MetallicCutoff.recoveryMap_silver_gt
#print axioms MetallicCutoff.recoveryMap_three_lt
#print axioms MetallicCutoff.strictAntiOn_scaledRecoveryRatio
#print axioms MetallicCutoff.existsUnique_even_fixed_point
#print axioms MetallicCutoff.evenFixedPoint_spec
#print axioms MetallicCutoff.eq_evenFixedPoint_of_fixed

-- Metallic cutoff Phase C2A: spectral form and convergence of the fixed point (Target 7A)
#print axioms MetallicCutoff.positiveFixedRoot
#print axioms MetallicCutoff.negativeFixedRoot
#print axioms MetallicCutoff.rowSpectralRatio
#print axioms MetallicCutoff.rowSpectralRatio_mem_unitInterval
#print axioms MetallicCutoff.ratio_spectral_decomposition
#print axioms MetallicCutoff.roots_and_ratio_at_three
#print axioms MetallicCutoff.recoveryMap_sub_positiveFixedRoot_bound
#print axioms MetallicCutoff.tendstoUniformlyOn_recoveryMap
#print axioms MetallicCutoff.positiveFixedRoot_recovery_fixed_iff
#print axioms MetallicCutoff.evenFixedPoint_sub_silver_bound
#print axioms MetallicCutoff.tendsto_evenFixedPoint

-- Metallic cutoff Phase C2B: sharp asymptotic coefficient of the fixed point (Target 7B)
#print axioms MetallicCutoff.evenFixedPointDelta
#print axioms MetallicCutoff.evenFixedPointRoot
#print axioms MetallicCutoff.evenFixedPointSpectralRatio
#print axioms MetallicCutoff.silver_lt_evenFixedPoint
#print axioms MetallicCutoff.tendsto_evenFixedPointDelta
#print axioms MetallicCutoff.tendsto_evenFixedPointRoot
#print axioms MetallicCutoff.tendsto_scaled_evenFixedPointSpectralRatio_pow
#print axioms MetallicCutoff.tendsto_scaled_evenFixedPoint_recovery_defect
#print axioms MetallicCutoff.evenFixedPoint_factorization
#print axioms MetallicCutoff.tendsto_evenFixedPoint_correctionFactor
#print axioms MetallicCutoff.tendsto_scaled_evenFixedPoint_sub_silver

-- Metallic cutoff Phase C3: transverse scale and the canonical cutoff (Target 8)
#print axioms MetallicCutoff.evenFixedPointTransversePerturbation
#print axioms MetallicCutoff.evenFixedPointTransverseDelta
#print axioms MetallicCutoff.evenFixedPointTransversePerturbation_eq
#print axioms MetallicCutoff.evenFixedPointTransverseDelta_lt_neg_one
#print axioms MetallicCutoff.tendsto_scaled_evenFixedPointTransversePerturbation
#print axioms MetallicCutoff.tendsto_evenFixedPointTransverseDelta
#print axioms MetallicCutoff.tendsto_evenFixedPoint_cutoff_signed
#print axioms MetallicCutoff.tendsto_evenFixedPoint_cutoff

-- Paper-facing gd3/gd4 exponential bridges and quotient autonomous laws
#print axioms SliceHyperbolic.gd3_exponential_bridge
#print axioms SliceHyperbolic.gd4_exponential_bridge
#print axioms SliceHyperbolic.gd3_quotient_ode
#print axioms SliceHyperbolic.gd4_quotient_ode

-- Pointwise logarithmic sublattice support and exact filter annihilation
#print axioms ResidueSlices.normalizedPositiveDFT
#print axioms ResidueSlices.positiveDFT_injective
#print axioms ResidueSlices.sublatticeProjector_eq_self_of_supported
#print axioms ResidueSlices.sublatticeProjector_pointwise_map
#print axioms ResidueSlices.positiveDFT_pointwise_map_supported_of_supported
#print axioms ResidueSlices.positiveDFT_log_one_add_supported_of_supported
#print axioms ResidueSlices.packetFilterValue
#print axioms ResidueSlices.inverse_normalizedPositiveDFT
#print axioms ResidueSlices.weighted_inverse_fourier_sum
#print axioms ResidueSlices.logarithmic_estimator_annihilated

-- Generic logarithmic sublattice and infinite convolution bridge
#print axioms ResidueSlices.logarithmicConvolutionCoeff
#print axioms ResidueSlices.logarithmicConvolutionSpectrum
#print axioms ResidueSlices.normalizedPositiveDFT_pointwise_mul
#print axioms ResidueSlices.normalizedPositiveDFT_pointwise_pow
#print axioms ResidueSlices.normalizedPositiveDFT_truncatedLog
#print axioms ResidueSlices.summable_logarithmicConvolutionSpectrum
#print axioms ResidueSlices.normalizedPositiveDFT_log_one_add
#print axioms ResidueSlices.logarithmicConvolutionSpectrum_supported
#print axioms ResidueSlices.normalizedPositiveDFT_log_one_add_supported
#print axioms ResidueSlices.packetFilterValue_eq_positive_at_neg
#print axioms ResidueSlices.logarithmic_estimator_annihilated_of_norm_lt_one
#print axioms ResidueSlices.eventually_logarithmic_estimator_annihilated

-- Cubic-silver finite-row crossover Phase B1: relative normalized center-remainder transfer
#print axioms SilverFiniteRow.tendsto_movingCrossoverScale
#print axioms SilverFiniteRow.tendsto_movingMuShift
#print axioms SilverFiniteRow.tendsto_movingDelta
#print axioms SilverFiniteRow.eventually_moving_affineInput_pos
#print axioms SilverFiniteRow.tendsto_moving_fixedPointFactor
#print axioms SilverFiniteRow.relativeCenterRemainder_le
#print axioms SilverFiniteRow.tendsto_relativeCenterRemainder_of_relativeDeviationVariation

-- Cubic-silver finite-row crossover: exact derivative bridge
#print axioms SilverFiniteRow.hasDerivAt_packetRatio
#print axioms SilverFiniteRow.hasDerivAt_cubeRoot
#print axioms SilverFiniteRow.hasDerivAt_packetErrorFunction
#print axioms SilverFiniteRow.packetDeviation_eq_packetErrorFunction
#print axioms SilverFiniteRow.deviationVariation_eq_packetErrorFunction_sub
#print axioms SilverFiniteRow.hasDerivAt_packetDeviation
#print axioms SilverFiniteRow.deviationVariation_eq_deriv_mul

-- Cubic-silver finite-row crossover Phase B2B: adjacent-row noncancellation
#print axioms SilverFiniteRow.centerT_pos
#print axioms SilverFiniteRow.centerOmega_isPrimitiveRoot
#print axioms SilverFiniteRow.centerChannel_ne_zero
#print axioms SilverFiniteRow.centerRho_pos
#print axioms SilverFiniteRow.packetRatio_center_numerator_wave
#print axioms SilverFiniteRow.packetRatio_center_denominator_wave
#print axioms SilverFiniteRow.centerDenominatorWave_pos
#print axioms SilverFiniteRow.packetRatio_center_channel_formula
#print axioms SilverFiniteRow.centerError_channel_formula
#print axioms SilverFiniteRow.centerRho_mem_unitInterval
#print axioms SilverFiniteRow.centerEndpointRate_nonneg
#print axioms SilverFiniteRow.centerEndpointRate_lt_one
#print axioms SilverFiniteRow.centerEndpointRate_lt_centerRho
#print axioms SilverFiniteRow.norm_centerUnitChannel
#print axioms SilverFiniteRow.centerUnitChannel_im_ne_zero
#print axioms SilverFiniteRow.centerProjectionConstant_pos
#print axioms SilverFiniteRow.adjacent_real_projection_lower
#print axioms SilverFiniteRow.adjacent_center_projection_lower
#print axioms SilverFiniteRow.tendsto_centerDenominatorWave
#print axioms SilverFiniteRow.tendsto_centerEndpointTerm_div_rho_pow
#print axioms SilverFiniteRow.eventually_adjacent_centerError_guard

-- Cubic-silver finite-row crossover Phase B2C: local derivative spectral rate
#print axioms SilverFiniteRow.localDerivativeRate_separation
#print axioms SilverFiniteRow.centerHalfRate_pos
#print axioms SilverFiniteRow.localDerivativeRate_pos
#print axioms SilverFiniteRow.localDerivativeRate_lt_one
#print axioms SilverFiniteRow.centerError_eq_packetErrorFunction
#print axioms SilverFiniteRow.hasDerivAt_centerError_parameter
#print axioms SilverFiniteRow.centerOfReal_add_one_ne_zero
#print axioms SilverFiniteRow.centerChannel_eq_div
#print axioms SilverFiniteRow.centerEndpointRate_eq_inv
#print axioms SilverFiniteRow.hasDerivAt_complexRe
#print axioms SilverFiniteRow.hasDerivAt_centerChannel
#print axioms SilverFiniteRow.hasDerivAt_centerEndpointRate
#print axioms SilverFiniteRow.hasDerivAt_centerChannel_pow
#print axioms SilverFiniteRow.hasDerivAt_centerEndpointRate_pow
#print axioms SilverFiniteRow.hasDerivAt_centerEndpointTerm
#print axioms SilverFiniteRow.hasDerivAt_centerNumeratorTerm
#print axioms SilverFiniteRow.hasDerivAt_centerDenominatorWave
#print axioms SilverFiniteRow.centerError_eq_quotient
#print axioms SilverFiniteRow.hasDerivAt_centerError_quotient
#print axioms SilverFiniteRow.packetErrorDerivative_eq_centerErrorParameterDeriv
#print axioms SilverFiniteRow.norm_centerChannelDeriv_le
#print axioms SilverFiniteRow.abs_centerEndpointRateDeriv_le
#print axioms SilverFiniteRow.epsIdx_bounds
#print axioms SilverFiniteRow.abs_sub_le_abs_add_abs
#print axioms SilverFiniteRow.abs_two_mul_re_le
#print axioms SilverFiniteRow.norm_centerChannel_pow_le
#print axioms SilverFiniteRow.abs_centerEndpointTerm_le
#print axioms SilverFiniteRow.abs_centerEndpointTermDeriv_le
#print axioms SilverFiniteRow.norm_centerChannelBlock_le
#print axioms SilverFiniteRow.abs_centerNumeratorTerm_le
#print axioms SilverFiniteRow.abs_centerNumeratorTermDeriv_le
#print axioms SilverFiniteRow.abs_centerDenominatorWaveDeriv_le
#print axioms SilverFiniteRow.abs_centerDenominatorWave_sub_one_le
#print axioms SilverFiniteRow.abs_quotient_estimate
#print axioms SilverFiniteRow.centerError_geometric_upper
#print axioms SilverFiniteRow.tendsto_natSucc_mul_pow
#print axioms SilverFiniteRow.tendsto_localDerivativeRate_div_centerHalfRate
#print axioms SilverFiniteRow.packetErrorDerivative_local_geometric_bound
#print axioms SilverFiniteRow.exists_centerError_and_localDerivative_bounds

-- Cubic-silver finite-row crossover Phase B2D: adaptive adjacent-row selection
#print axioms SilverFiniteRow.adaptiveRow_eq_self_or_succ
#print axioms SilverFiniteRow.le_adaptiveRow
#print axioms SilverFiniteRow.adaptiveRow_le_succ
#print axioms SilverFiniteRow.normalizedCenterError_adaptiveRow_eq_max
#print axioms SilverFiniteRow.tendsto_adaptiveRow
#print axioms SilverFiniteRow.eventually_adaptiveRow_normalized_guard
#print axioms SilverFiniteRow.eventually_adaptiveRow_centerError_lower
#print axioms SilverFiniteRow.eventually_adaptiveRow_centerError_upper
#print axioms SilverFiniteRow.eventually_adaptiveRow_centerError_ne_zero
#print axioms SilverFiniteRow.eventually_adaptiveRow_packetErrorDerivative_bound
#print axioms SilverFiniteRow.tendsto_adaptiveRow_localDerivativeRate_div_centerHalfRate

-- Cubic-silver finite-row crossover Phase B3: selected relative deviation and center-remainder convergence
#print axioms SilverFiniteRow.tendsto_relativeCenterRemainder_of_reindexed_relativeDeviationVariation
#print axioms SilverFiniteRow.eventually_adaptiveRow_relativeDeviationVariation_bound
#print axioms SilverFiniteRow.eventually_adaptiveRow_relativeDeviationVariation_lt
#print axioms SilverFiniteRow.tendsto_adaptiveRow_relativeDeviationVariation
#print axioms SilverFiniteRow.tendsto_adaptiveRow_relativeCenterRemainder

-- Cubic-silver finite-row crossover Phase B4A: silver finite-row fixed-point convergence
#print axioms SilverFiniteRow.silverFiniteRowFixedPoint
#print axioms SilverFiniteRow.limitingMap_sub_self_pos_of_lt
#print axioms SilverFiniteRow.limitingMap_sub_self_neg_of_lt
#print axioms SilverFiniteRow.eventually_finiteMap_bracket_sign
#print axioms SilverFiniteRow.eventually_all_finiteRow_fixedPoints_near
#print axioms SilverFiniteRow.silverFiniteRowFixedPoint_spec
#print axioms SilverFiniteRow.tendsto_silverFiniteRowFixedPoint

-- Cubic-silver finite-row crossover Phase B4B1: fixed-point converse and normalized crossover residual
#print axioms SilverFiniteRow.signedRelativeCenterRemainder
#print axioms SilverFiniteRow.normalizedCrossoverResidual
#print axioms SilverFiniteRow.fixedPointFactor_pos_of_affineInput_pos
#print axioms SilverFiniteRow.finiteMap_eq_self_iff_quadraticCrossover_eq_centerRemainder
#print axioms SilverFiniteRow.abs_signedRelativeCenterRemainder
#print axioms SilverFiniteRow.tendsto_adaptiveRow_signedRelativeCenterRemainder
#print axioms SilverFiniteRow.normalizedCrossoverResidual_eq_zero_iff_fixed
#print axioms SilverFiniteRow.normalizedCrossoverResidual_eq_positive
#print axioms SilverFiniteRow.normalizedCrossoverResidual_eq_negative
#print axioms SilverFiniteRow.tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_positive
#print axioms SilverFiniteRow.tendsto_reindexed_adaptiveRow_normalizedCrossoverResidual_negative

-- Cubic-silver finite-row crossover Phase B4B2: local crossover-root stability near simple limiting roots
#print axioms SilverFiniteRow.eventually_reindexed_adaptiveRow_affineInput_pos_on_Icc
#print axioms SilverFiniteRow.continuousOn_normalizedCrossoverResidual
#print axioms SilverFiniteRow.eventually_reindexed_normalizedCrossoverResidual_bracket_positive
#print axioms SilverFiniteRow.eventually_reindexed_normalizedCrossoverResidual_bracket_negative
#print axioms SilverFiniteRow.eventually_exists_positive_crossover_fixedPoint_in_bracket
#print axioms SilverFiniteRow.eventually_exists_negative_crossover_fixedPoint_in_bracket
#print axioms SilverFiniteRow.eventually_exists_positive_crossover_fixedPoint_near_simple_root
#print axioms SilverFiniteRow.eventually_exists_negative_crossover_fixedPoint_near_simple_root

-- Cubic-silver finite-row crossover Phase B4B3: select one convergent crossover branch
#print axioms SilverFiniteRow.exists_tendsto_selection_of_eventually_exists_near
#print axioms SilverFiniteRow.tendsto_reindexed_moving_fixedPoint_value
#print axioms SilverFiniteRow.exists_tendsto_positive_crossover_fixedPoint_branch
#print axioms SilverFiniteRow.exists_tendsto_negative_crossover_fixedPoint_branch

-- Cubic-silver finite-row crossover Phase B4B4: explicit real quadratic-root crossover branches
#print axioms SilverFiniteRow.positiveCrossoverRootPlus_spec
#print axioms SilverFiniteRow.positiveCrossoverRootMinus_spec
#print axioms SilverFiniteRow.negativeCrossoverRootPlus_spec_of_two_lt_abs
#print axioms SilverFiniteRow.negativeCrossoverRootMinus_spec_of_two_lt_abs
#print axioms SilverFiniteRow.exists_tendsto_positive_crossover_fixedPoint_branch_plus
#print axioms SilverFiniteRow.exists_tendsto_positive_crossover_fixedPoint_branch_minus
#print axioms SilverFiniteRow.exists_tendsto_negative_crossover_fixedPoint_branch_plus_of_two_lt_abs
#print axioms SilverFiniteRow.exists_tendsto_negative_crossover_fixedPoint_branch_minus_of_two_lt_abs
