/-
Axiom audit for all 193 public theorem/lemma declarations. Run with:
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
-- Keeping them explicit makes this driver a 193/193 public-proof audit.
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
