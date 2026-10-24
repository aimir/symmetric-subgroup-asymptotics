import SymmetricSubgroupAsymptotics.BinaryGeneralLinearSmallExactMultiplicities
import Mathlib.Tactic.IntervalCases

/-! Two joint strict budgets extracted from the already checked literal
GL orders in dimensions four through six. The statements concern the
same total and matching valuations, not independent local groups or
supplied generator certificates. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryGeneralLinearOddSmallStrictMultiplicities
open OriginalBinaryAffineDominantDivisorCost (totalMultiplicity)
open BinaryGeneralLinearMatchingPrimeMultiplicity
open BinaryGeneralLinearSmallExactMultiplicities

theorem total_le_square_sub_two (d : ℕ) (hd4 : 4 ≤ d) (hd6 : d ≤ 6) :
    totalMultiplicity d ≤ d^2-2 := by
  interval_cases d
  all_goals
    rw [totalMultiplicity_eq _ (by decide)]
    decide

theorem matching_odd_le_sub_two (d q : ℕ) (hd4 : 4 ≤ d) (hd6 : d ≤ 6) (hq : q ≠ 2) :
    matchingMultiplicity d q ≤ d-2 := by
  rw [matching_odd_eq d q hd6 hq]
  interval_cases d <;> unfold smallOddMatching <;> split_ifs <;> omega

end SymmetricSubgroupAsymptotics.BinaryGeneralLinearOddSmallStrictMultiplicities
