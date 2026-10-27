import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourIndexedPointFibreCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirstZeroWhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst1WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst2WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst3WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst4WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst5WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst6WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst7WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst8WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst9WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst10WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst11WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst12WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst13WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst14WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst15WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst16WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst17WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst18WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst19WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst20WhitelistCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourFirst21WhitelistCapacity
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourCompleteWhitelistCapacity
open CFSGMathieuTwentyFourPackedPrefixCertificate CFSGMathieuTwentyFourIndexedPointFibreCapacity
open CFSGMathieuTwentyTwoFiveTransversalCover

def failure (i : First) (j : Second) : Selector :=
  match i.val with
  | 0 => CFSGMathieuTwentyFourFirstZeroWhitelistCapacity.failure j
  | 1 => CFSGMathieuTwentyFourFirst1WhitelistCapacity.failure j
  | 2 => CFSGMathieuTwentyFourFirst2WhitelistCapacity.failure j
  | 3 => CFSGMathieuTwentyFourFirst3WhitelistCapacity.failure j
  | 4 => CFSGMathieuTwentyFourFirst4WhitelistCapacity.failure j
  | 5 => CFSGMathieuTwentyFourFirst5WhitelistCapacity.failure j
  | 6 => CFSGMathieuTwentyFourFirst6WhitelistCapacity.failure j
  | 7 => CFSGMathieuTwentyFourFirst7WhitelistCapacity.failure j
  | 8 => CFSGMathieuTwentyFourFirst8WhitelistCapacity.failure j
  | 9 => CFSGMathieuTwentyFourFirst9WhitelistCapacity.failure j
  | 10 => CFSGMathieuTwentyFourFirst10WhitelistCapacity.failure j
  | 11 => CFSGMathieuTwentyFourFirst11WhitelistCapacity.failure j
  | 12 => CFSGMathieuTwentyFourFirst12WhitelistCapacity.failure j
  | 13 => CFSGMathieuTwentyFourFirst13WhitelistCapacity.failure j
  | 14 => CFSGMathieuTwentyFourFirst14WhitelistCapacity.failure j
  | 15 => CFSGMathieuTwentyFourFirst15WhitelistCapacity.failure j
  | 16 => CFSGMathieuTwentyFourFirst16WhitelistCapacity.failure j
  | 17 => CFSGMathieuTwentyFourFirst17WhitelistCapacity.failure j
  | 18 => CFSGMathieuTwentyFourFirst18WhitelistCapacity.failure j
  | 19 => CFSGMathieuTwentyFourFirst19WhitelistCapacity.failure j
  | 20 => CFSGMathieuTwentyFourFirst20WhitelistCapacity.failure j
  | 21 => CFSGMathieuTwentyFourFirst21WhitelistCapacity.failure j
  | _ => CFSGMathieuTwentyFourFirstZeroWhitelistCapacity.failure j

def whitelist (i : First) (j : Second) : List RawTail :=
  match i.val with
  | 0 => CFSGMathieuTwentyFourFirstZeroWhitelistCapacity.whitelist j
  | 1 => CFSGMathieuTwentyFourFirst1WhitelistCapacity.whitelist j
  | 2 => CFSGMathieuTwentyFourFirst2WhitelistCapacity.whitelist j
  | 3 => CFSGMathieuTwentyFourFirst3WhitelistCapacity.whitelist j
  | 4 => CFSGMathieuTwentyFourFirst4WhitelistCapacity.whitelist j
  | 5 => CFSGMathieuTwentyFourFirst5WhitelistCapacity.whitelist j
  | 6 => CFSGMathieuTwentyFourFirst6WhitelistCapacity.whitelist j
  | 7 => CFSGMathieuTwentyFourFirst7WhitelistCapacity.whitelist j
  | 8 => CFSGMathieuTwentyFourFirst8WhitelistCapacity.whitelist j
  | 9 => CFSGMathieuTwentyFourFirst9WhitelistCapacity.whitelist j
  | 10 => CFSGMathieuTwentyFourFirst10WhitelistCapacity.whitelist j
  | 11 => CFSGMathieuTwentyFourFirst11WhitelistCapacity.whitelist j
  | 12 => CFSGMathieuTwentyFourFirst12WhitelistCapacity.whitelist j
  | 13 => CFSGMathieuTwentyFourFirst13WhitelistCapacity.whitelist j
  | 14 => CFSGMathieuTwentyFourFirst14WhitelistCapacity.whitelist j
  | 15 => CFSGMathieuTwentyFourFirst15WhitelistCapacity.whitelist j
  | 16 => CFSGMathieuTwentyFourFirst16WhitelistCapacity.whitelist j
  | 17 => CFSGMathieuTwentyFourFirst17WhitelistCapacity.whitelist j
  | 18 => CFSGMathieuTwentyFourFirst18WhitelistCapacity.whitelist j
  | 19 => CFSGMathieuTwentyFourFirst19WhitelistCapacity.whitelist j
  | 20 => CFSGMathieuTwentyFourFirst20WhitelistCapacity.whitelist j
  | 21 => CFSGMathieuTwentyFourFirst21WhitelistCapacity.whitelist j
  | _ => CFSGMathieuTwentyFourFirstZeroWhitelistCapacity.whitelist j

theorem all_batches (i : First) (j : Second) :
    batchCheck i.val j.val.val (failure i j) (whitelist i j)=true := by
  fin_cases i
  · exact CFSGMathieuTwentyFourFirstZeroWhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst1WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst2WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst3WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst4WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst5WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst6WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst7WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst8WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst9WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst10WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst11WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst12WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst13WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst14WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst15WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst16WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst17WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst18WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst19WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst20WhitelistCapacity.all_batches j
  · exact CFSGMathieuTwentyFourFirst21WhitelistCapacity.all_batches j

/-- Exact sum of the literal whitelists, computed by the kernel. -/
def computedTotal : ℕ := 1

/-- Kernel-checked numerical margin; the actual whitelist total is not assumed. -/
theorem computedTotal_le_six : computedTotal ≤ 6 := by decide +kernel

theorem whitelist_length_sum :
    (∑ i : First, ∑ j : Second, (whitelist i j).length)=computedTotal := by decide +kernel

theorem swap_card_le_sum [IsSimpleGroup CFSG.Models.Presentations.M24.Model] :
    Nat.card CFSGMathieuTwentyFourSwapFibreOuterReduction.SwapFibre ≤
      ∑ i : First, ∑ j : Second, (whitelist i j).length :=
  swapFibre_card_le_whitelist_sum failure whitelist all_batches

theorem swap_card_le_total [IsSimpleGroup CFSG.Models.Presentations.M24.Model] :
    Nat.card CFSGMathieuTwentyFourSwapFibreOuterReduction.SwapFibre ≤ computedTotal := by
  rw [←whitelist_length_sum]
  exact swap_card_le_sum

theorem outer_card_le_twice_total [Finite CFSG.Models.Presentations.M24.Model]
    [IsSimpleGroup CFSG.Models.Presentations.M24.Model] :
    Nat.card (PrimitiveSocleRawStructure.Outer CFSG.Models.Presentations.M24.Model) ≤ 2*computedTotal :=
  CFSGMathieuTwentyFourSwapFibreOuterReduction.outer_card_le_twice_swap.trans
    (Nat.mul_le_mul_left 2 swap_card_le_total)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourCompleteWhitelistCapacity
