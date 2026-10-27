import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstZeroCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstOneCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstTwoCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstThreeCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstFourCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstFiveCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstSixCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstSevenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstEightCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstNineCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstTenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstElevenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstTwelveCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstThirteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstFourteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstFifteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstSixteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstSeventeenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstEighteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstNineteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstTwentyCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeFirstTwentyOneCapacity

/-! All 22 actual first addresses, with variable literal second-address
whitelists. These lists bound genuine pinned fixed-product automorphisms via
their original faithful action; survivors need not be automorphisms. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedFullPointFibreCapacity
open scoped BigOperators
open CFSGMathieuTwentyThreeStabilizerTransversalCover
open CFSGMathieuTwentyThreePackedPrefixCertificate
open CFSGMathieuTwentyThreeIndexedPointFibreCapacity
open CFSGMathieuTwentyThreeNormalizedFixedPointFibre

def failure (i : First) (j : Second) : Selector :=
  match i.val.val with
  | 0 => CFSGMathieuTwentyThreeFirstZeroCapacity.failure j.val.val
  | 1 => CFSGMathieuTwentyThreeFirstOneCapacity.failure j.val.val
  | 2 => CFSGMathieuTwentyThreeFirstTwoCapacity.failure j.val.val
  | 3 => CFSGMathieuTwentyThreeFirstThreeCapacity.failure j.val.val
  | 4 => CFSGMathieuTwentyThreeFirstFourCapacity.failure j.val.val
  | 5 => CFSGMathieuTwentyThreeFirstFiveCapacity.failure j.val.val
  | 6 => CFSGMathieuTwentyThreeFirstSixCapacity.failure j.val.val
  | 7 => CFSGMathieuTwentyThreeFirstSevenCapacity.failure j.val.val
  | 8 => CFSGMathieuTwentyThreeFirstEightCapacity.failure j.val.val
  | 9 => CFSGMathieuTwentyThreeFirstNineCapacity.failure j.val.val
  | 10 => CFSGMathieuTwentyThreeFirstTenCapacity.failure j.val.val
  | 11 => CFSGMathieuTwentyThreeFirstElevenCapacity.failure j.val.val
  | 12 => CFSGMathieuTwentyThreeFirstTwelveCapacity.failure j.val.val
  | 13 => CFSGMathieuTwentyThreeFirstThirteenCapacity.failure j.val.val
  | 14 => CFSGMathieuTwentyThreeFirstFourteenCapacity.failure j.val.val
  | 15 => CFSGMathieuTwentyThreeFirstFifteenCapacity.failure j.val.val
  | 16 => CFSGMathieuTwentyThreeFirstSixteenCapacity.failure j.val.val
  | 17 => CFSGMathieuTwentyThreeFirstSeventeenCapacity.failure j.val.val
  | 18 => CFSGMathieuTwentyThreeFirstEighteenCapacity.failure j.val.val
  | 19 => CFSGMathieuTwentyThreeFirstNineteenCapacity.failure j.val.val
  | 20 => CFSGMathieuTwentyThreeFirstTwentyCapacity.failure j.val.val
  | 21 => CFSGMathieuTwentyThreeFirstTwentyOneCapacity.failure j.val.val
  | _ => fun _ _ _ => 0

def whitelist (i : First) (j : Second) : List RawTail :=
  match i.val.val with
  | 0 => CFSGMathieuTwentyThreeFirstZeroCapacity.whitelist j.val.val
  | 1 => CFSGMathieuTwentyThreeFirstOneCapacity.whitelist j.val.val
  | 2 => CFSGMathieuTwentyThreeFirstTwoCapacity.whitelist j.val.val
  | 3 => CFSGMathieuTwentyThreeFirstThreeCapacity.whitelist j.val.val
  | 4 => CFSGMathieuTwentyThreeFirstFourCapacity.whitelist j.val.val
  | 5 => CFSGMathieuTwentyThreeFirstFiveCapacity.whitelist j.val.val
  | 6 => CFSGMathieuTwentyThreeFirstSixCapacity.whitelist j.val.val
  | 7 => CFSGMathieuTwentyThreeFirstSevenCapacity.whitelist j.val.val
  | 8 => CFSGMathieuTwentyThreeFirstEightCapacity.whitelist j.val.val
  | 9 => CFSGMathieuTwentyThreeFirstNineCapacity.whitelist j.val.val
  | 10 => CFSGMathieuTwentyThreeFirstTenCapacity.whitelist j.val.val
  | 11 => CFSGMathieuTwentyThreeFirstElevenCapacity.whitelist j.val.val
  | 12 => CFSGMathieuTwentyThreeFirstTwelveCapacity.whitelist j.val.val
  | 13 => CFSGMathieuTwentyThreeFirstThirteenCapacity.whitelist j.val.val
  | 14 => CFSGMathieuTwentyThreeFirstFourteenCapacity.whitelist j.val.val
  | 15 => CFSGMathieuTwentyThreeFirstFifteenCapacity.whitelist j.val.val
  | 16 => CFSGMathieuTwentyThreeFirstSixteenCapacity.whitelist j.val.val
  | 17 => CFSGMathieuTwentyThreeFirstSeventeenCapacity.whitelist j.val.val
  | 18 => CFSGMathieuTwentyThreeFirstEighteenCapacity.whitelist j.val.val
  | 19 => CFSGMathieuTwentyThreeFirstNineteenCapacity.whitelist j.val.val
  | 20 => CFSGMathieuTwentyThreeFirstTwentyCapacity.whitelist j.val.val
  | 21 => CFSGMathieuTwentyThreeFirstTwentyOneCapacity.whitelist j.val.val
  | _ => []

theorem all_second_checks (i : First) (j : Second) :
    batchCheck i.val.val j.val.val (failure i j) (whitelist i j) = true := by
  rcases i with ⟨i,hi⟩
  fin_cases i
  · exact CFSGMathieuTwentyThreeFirstZeroCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstOneCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstTwoCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstThreeCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstFourCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstFiveCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstSixCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstSevenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstEightCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstNineCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstTenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstElevenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstTwelveCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstThirteenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstFourteenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstFifteenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstSixteenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstSeventeenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstEighteenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstNineteenCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstTwentyCapacity.all_second_checks j
  · exact CFSGMathieuTwentyThreeFirstTwentyOneCapacity.all_second_checks j
  · exact (hi rfl).elim

def literalGrandTotal : ℕ := 7

theorem whitelist_sum_eq_count :
    (∑ i : First, ∑ j : Second, (whitelist i j).length) = literalGrandTotal := by
  decide +kernel

theorem pointFibre_card_le_count [IsSimpleGroup CFSG.Models.Presentations.M23.Model] :
    Nat.card (pointFibre 0) ≤ literalGrandTotal := by
  calc
    _ ≤ ∑ i : First, ∑ j : Second, (whitelist i j).length :=
      pointFibre_card_le_whitelist_sum failure whitelist all_second_checks
    _ = _ := whitelist_sum_eq_count

theorem pointFibre_card_le_twenty [IsSimpleGroup CFSG.Models.Presentations.M23.Model] :
    Nat.card (pointFibre 0) ≤ 20 :=
  pointFibre_card_le_count.trans (by decide +kernel)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedFullPointFibreCapacity
