import SymmetricSubgroupAsymptotics.FiniteIndexedAutomorphismImageCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoIncidenceNoFixedPoint
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixOneCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixTwoCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixThreeCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixFourCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixFiveCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixSixCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixSevenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixEightCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixNineCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixTenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixElevenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixTwelveCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixThirteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixFourteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixFifteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixSixteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixSeventeenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixEighteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixNineteenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixTwentyCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPrefixTwentyOneCapacity

/-! Complete actual fixed-generator capacity. Every nonzero decoder prefix
has its own kernel-checked sparse certificate; prefix zero is excluded for
genuine automorphism images by the original action's fixed-point theorem.
The finite-index image count allows overlaps, so no ownership or disjointness
hypothesis is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedFullCapacity
open CFSGMathieuTwentyTwoElevenGeneration CFSGMathieuTwentyTwoFiveTransversalCover
open OuterFixedElementEvaluationBound

def acceptedAt (i : Fin 22) : Finset CFSG.Models.Mathieu22 :=
  match i.val with
  | 1 => CFSGMathieuTwentyTwoPackedPrefixOneCapacity.acceptedElements
  | 2 => CFSGMathieuTwentyTwoPackedPrefixTwoCapacity.acceptedElements
  | 3 => CFSGMathieuTwentyTwoPackedPrefixThreeCapacity.acceptedElements
  | 4 => CFSGMathieuTwentyTwoPackedPrefixFourCapacity.acceptedElements
  | 5 => CFSGMathieuTwentyTwoPackedPrefixFiveCapacity.acceptedElements
  | 6 => CFSGMathieuTwentyTwoPackedPrefixSixCapacity.acceptedElements
  | 7 => CFSGMathieuTwentyTwoPackedPrefixSevenCapacity.acceptedElements
  | 8 => CFSGMathieuTwentyTwoPackedPrefixEightCapacity.acceptedElements
  | 9 => CFSGMathieuTwentyTwoPackedPrefixNineCapacity.acceptedElements
  | 10 => CFSGMathieuTwentyTwoPackedPrefixTenCapacity.acceptedElements
  | 11 => CFSGMathieuTwentyTwoPackedPrefixElevenCapacity.acceptedElements
  | 12 => CFSGMathieuTwentyTwoPackedPrefixTwelveCapacity.acceptedElements
  | 13 => CFSGMathieuTwentyTwoPackedPrefixThirteenCapacity.acceptedElements
  | 14 => CFSGMathieuTwentyTwoPackedPrefixFourteenCapacity.acceptedElements
  | 15 => CFSGMathieuTwentyTwoPackedPrefixFifteenCapacity.acceptedElements
  | 16 => CFSGMathieuTwentyTwoPackedPrefixSixteenCapacity.acceptedElements
  | 17 => CFSGMathieuTwentyTwoPackedPrefixSeventeenCapacity.acceptedElements
  | 18 => CFSGMathieuTwentyTwoPackedPrefixEighteenCapacity.acceptedElements
  | 19 => CFSGMathieuTwentyTwoPackedPrefixNineteenCapacity.acceptedElements
  | 20 => CFSGMathieuTwentyTwoPackedPrefixTwentyCapacity.acceptedElements
  | 21 => CFSGMathieuTwentyTwoPackedPrefixTwentyOneCapacity.acceptedElements
  | _ => ∅

theorem acceptedAt_card_le_two (i : Fin 22) : (acceptedAt i).card ≤ 2 := by
  fin_cases i
  · exact Nat.zero_le _
  · exact CFSGMathieuTwentyTwoPackedPrefixOneCapacity.acceptedElements_card_le_one.trans (by decide)
  · exact CFSGMathieuTwentyTwoPackedPrefixTwoCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixThreeCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixFourCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixFiveCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixSixCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixSevenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixEightCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixNineCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixTenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixElevenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixTwelveCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixThirteenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixFourteenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixFifteenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixSixteenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixSeventeenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixEighteenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixNineteenCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixTwentyCapacity.acceptedElements_card_le_two
  · exact CFSGMathieuTwentyTwoPackedPrefixTwentyOneCapacity.acceptedElements_card_le_two

theorem map_second_mem_acceptedAt
    (f : MulAut CFSG.Models.Mathieu22) (hf : f firstElement = firstElement)
    (c : Code) (hc : decode c = f secondElement) :
    f secondElement ∈ acceptedAt c.1.1 := by
  have hn := CFSGMathieuTwentyTwoIncidenceNoFixedPoint.first_prefix_ne_zero f c hc
  generalize hi : c.1.1 = i
  fin_cases i
  · exact (hn hi).elim
  · exact CFSGMathieuTwentyTwoPackedPrefixOneCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixTwoCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixThreeCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixFourCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixFiveCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixSixCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixSevenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixEightCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixNineCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixTenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixElevenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixTwelveCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixThirteenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixFourteenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixFifteenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixSixteenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixSeventeenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixEighteenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixNineteenCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixTwentyCapacity.map_second_mem_acceptedElements f hf c hc hi
  · exact CFSGMathieuTwentyTwoPackedPrefixTwentyOneCapacity.map_second_mem_acceptedElements f hf c hc hi

theorem fixedAutomorphisms_card_le_fortyFour :
    Nat.card (fixedAutomorphisms firstElement) ≤ 44 := by
  have hg : Subgroup.closure ({secondElement,firstElement} : Set CFSG.Models.Mathieu22) = ⊤ := by
    simpa only [Set.pair_comm] using CFSGMathieuTwentyTwoSylowOuterNormalization.closure_pair_eq_top
  have h := FiniteIndexedAutomorphismImageCapacity.fixedAutomorphisms_card_le_sum
    secondElement firstElement hg acceptedAt (by
      intro f
      obtain ⟨c,hc⟩ := decode_surjective (f.val secondElement)
      exact ⟨c.1.1,map_second_mem_acceptedAt f.val f.property c hc⟩)
  apply h.trans
  calc
    ∑ i : Fin 22, (acceptedAt i).card ≤ ∑ _i : Fin 22, 2 :=
      Finset.sum_le_sum (fun i _ => acceptedAt_card_le_two i)
    _ = 44 := by simp

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedFullCapacity
