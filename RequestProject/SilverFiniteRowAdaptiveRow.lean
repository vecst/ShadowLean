/-
Cubic-silver finite-row crossover, Phase B2D: adaptive adjacent-row selection.
Selector infrastructure: bounded-delay adaptive row choice and transport of the
adjacent-pair guard, geometric upper bound, and local derivative estimates.
-/
import RequestProject.SilverFiniteRowLocalDerivativeRate

open scoped Real Topology BigOperators
open Filter

namespace SilverFiniteRow

noncomputable def normalizedCenterError (N : Nat) (alpha : Real) : Real :=
  |centerError N alpha| / centerRho alpha ^ N

noncomputable def adaptiveRow (N : Nat) (alpha : Real) : Nat :=
  if normalizedCenterError N alpha ≤ normalizedCenterError (N + 1) alpha then
    N + 1
  else
    N

theorem adaptiveRow_eq_self_or_succ (N : Nat) (alpha : Real) :
    adaptiveRow N alpha = N ∨ adaptiveRow N alpha = N + 1 := by
  unfold adaptiveRow
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem le_adaptiveRow (N : Nat) (alpha : Real) :
    N ≤ adaptiveRow N alpha := by
  unfold adaptiveRow
  split_ifs with h
  · exact Nat.le_succ N
  · exact le_rfl

theorem adaptiveRow_le_succ (N : Nat) (alpha : Real) :
    adaptiveRow N alpha ≤ N + 1 := by
  unfold adaptiveRow
  split_ifs with h
  · exact le_rfl
  · exact Nat.le_succ N

theorem normalizedCenterError_adaptiveRow_eq_max
    (N : Nat) (alpha : Real) :
    normalizedCenterError (adaptiveRow N alpha) alpha =
      max (normalizedCenterError N alpha)
        (normalizedCenterError (N + 1) alpha) := by
  unfold adaptiveRow
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (not_le.mp h).le).symm

theorem tendsto_adaptiveRow (alpha : Real) :
    Filter.Tendsto
      (fun N : Nat => adaptiveRow N alpha)
      Filter.atTop Filter.atTop := by
  exact tendsto_atTop_mono (fun N => le_adaptiveRow N alpha) tendsto_id

theorem eventually_adaptiveRow_normalized_guard
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ c : Real, 0 < c ∧
      ∀ᶠ N in Filter.atTop,
        c ≤ normalizedCenterError (adaptiveRow N alpha) alpha := by
  obtain ⟨c, hc, hev⟩ := eventually_adjacent_centerError_guard halpha
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with N hN
  rw [normalizedCenterError_adaptiveRow_eq_max]
  simpa [normalizedCenterError] using hN

theorem eventually_adaptiveRow_centerError_lower
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ c : Real, 0 < c ∧
      ∀ᶠ N in Filter.atTop,
        c * centerRho alpha ^ (adaptiveRow N alpha) ≤
          |centerError (adaptiveRow N alpha) alpha| := by
  have hrho : 0 < centerRho alpha := centerRho_pos (lt_trans one_pos halpha)
  obtain ⟨c, hc, hev⟩ := eventually_adaptiveRow_normalized_guard halpha
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev] with N hN
  have hp : 0 < centerRho alpha ^ (adaptiveRow N alpha) := pow_pos hrho _
  rw [normalizedCenterError, le_div_iff₀ hp] at hN
  exact hN

theorem eventually_adaptiveRow_centerError_upper
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ N in Filter.atTop,
        |centerError (adaptiveRow N alpha) alpha| ≤
          C * centerRho alpha ^ (adaptiveRow N alpha) := by
  obtain ⟨C, hC, N0, hN0⟩ := centerError_geometric_upper halpha
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  exact hN0 _ (le_trans hN (le_adaptiveRow N alpha))

theorem eventually_adaptiveRow_centerError_ne_zero
    {alpha : Real} (halpha : 1 < alpha) :
    ∀ᶠ N in Filter.atTop,
      centerError (adaptiveRow N alpha) alpha ≠ 0 := by
  have hrho : 0 < centerRho alpha := centerRho_pos (lt_trans one_pos halpha)
  obtain ⟨c, hc, hev⟩ := eventually_adaptiveRow_centerError_lower halpha
  filter_upwards [hev] with N hN
  have hp : 0 < centerRho alpha ^ (adaptiveRow N alpha) := pow_pos hrho _
  have hpos : 0 < |centerError (adaptiveRow N alpha) alpha| :=
    lt_of_lt_of_le (by positivity) hN
  exact abs_pos.mp hpos

theorem eventually_adaptiveRow_packetErrorDerivative_bound
    {alpha : Real} (halpha : 1 < alpha) :
    ∃ delta C : Real,
      0 < delta ∧ delta < alpha - 1 ∧ 0 < C ∧
      ∀ᶠ N in Filter.atTop,
        ∀ beta ∈ Set.Icc (alpha - delta) (alpha + delta),
          |packetErrorDerivative (adaptiveRow N alpha) (beta ^ 3)| ≤
            C * ((adaptiveRow N alpha + 1 : Nat) : Real) *
              localDerivativeRate alpha ^ (adaptiveRow N alpha) := by
  obtain ⟨delta, C, N0, hd, hd', hC, hbound⟩ :=
    packetErrorDerivative_local_geometric_bound halpha
  refine ⟨delta, C, hd, hd', hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN beta hbeta
  exact hbound _ (le_trans hN (le_adaptiveRow N alpha)) beta hbeta

theorem tendsto_adaptiveRow_localDerivativeRate_div_centerHalfRate
    {alpha : Real} (halpha : 0 < alpha) :
    Filter.Tendsto
      (fun N : Nat =>
        ((adaptiveRow N alpha + 1 : Nat) : Real) *
            localDerivativeRate alpha ^ (adaptiveRow N alpha) /
          centerHalfRate alpha ^ (adaptiveRow N alpha))
      Filter.atTop (nhds 0) := by
  have h :=
    (tendsto_localDerivativeRate_div_centerHalfRate halpha).comp (tendsto_adaptiveRow alpha)
  simpa [Function.comp_def] using h

end SilverFiniteRow
