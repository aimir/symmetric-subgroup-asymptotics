import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixZeroCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixOneCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixTwoCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixThreeCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixFourCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixFiveCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixSixCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixSevenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixEightCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixNineCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixTenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePrefixElevenCapacity
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualEquivalence
import SymmetricSubgroupAsymptotics.FiniteIndexedAutomorphismImageCapacity

/-! All twelve original-action prefix covers are kernel checked. Their
varying capacities sum to eleven. The dependent-sum evaluation counts
actual fixed-generator automorphisms without requiring disjoint covers or
a presentation converse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveAcceptedCodeCapacity
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelveFiveTransversalCover
open CFSGMathieuTwelveRecoveredPairRelations CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveActualRepresentation

theorem original_pair_generates : Subgroup.closure ({x,y} : Set M12) = ⊤ := by
  let R := Subgroup.closure ({x,y} : Set M12)
  have htop : (⊤ : Subgroup CFSG.Models.Presentations.M12.Model) ≤
      R.comap representation := by
    rw [←PresentedGroup.closure_range_of {w | w ∈ CFSG.Models.Presentations.M12.relators}]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change representation (PresentedGroup.of (0 : Fin 2)) ∈ R
      rw [representation_of_zero]
      exact Subgroup.subset_closure (by simp)
    · change representation (PresentedGroup.of (1 : Fin 2)) ∈ R
      rw [representation_of_one]
      exact Subgroup.subset_closure (by simp)
  apply top_unique
  intro g _
  obtain ⟨z,rfl⟩ := CFSGMathieuTwelveActualEquivalence.representation_surjective g
  exact htop (by trivial)

theorem fixed_pair_generates :
    Subgroup.closure ({secondElement,firstElement} : Set M12) = ⊤ := by
  have h := InvolutionTernaryProductShortRecovery.closure_product_conjugate_eq_top
    x y relator_zero relator_one original_pair_generates
  simpa only [firstElement,secondElement,Set.pair_comm] using h

def acceptedPrefix (i : Fin 12) : Finset M12 :=
  match i.val with
  | 0 => CFSGMathieuTwelvePrefixZeroCapacity.acceptedElements
  | 1 => CFSGMathieuTwelvePrefixOneCapacity.acceptedElements
  | 2 => CFSGMathieuTwelvePrefixTwoCapacity.acceptedElements
  | 3 => CFSGMathieuTwelvePrefixThreeCapacity.acceptedElements
  | 4 => CFSGMathieuTwelvePrefixFourCapacity.acceptedElements
  | 5 => CFSGMathieuTwelvePrefixFiveCapacity.acceptedElements
  | 6 => CFSGMathieuTwelvePrefixSixCapacity.acceptedElements
  | 7 => CFSGMathieuTwelvePrefixSevenCapacity.acceptedElements
  | 8 => CFSGMathieuTwelvePrefixEightCapacity.acceptedElements
  | 9 => CFSGMathieuTwelvePrefixNineCapacity.acceptedElements
  | 10 => CFSGMathieuTwelvePrefixTenCapacity.acceptedElements
  | _ => CFSGMathieuTwelvePrefixElevenCapacity.acceptedElements

theorem accepts_decode_mem_acceptedPrefix (c : Code) (h : Accepts (decode c)) :
    decode c ∈ acceptedPrefix c.1.1 := by
  rcases c with ⟨⟨i,j⟩,⟨k,⟨l,m⟩⟩⟩
  fin_cases i
  · exact CFSGMathieuTwelvePrefixZeroCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixOneCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixTwoCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixThreeCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixFourCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixFiveCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixSixCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixSevenCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixEightCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixNineCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixTenCapacity.accepts_mem_acceptedElements _ rfl h
  · exact CFSGMathieuTwelvePrefixElevenCapacity.accepts_mem_acceptedElements _ rfl h

def capacityAt (i : Fin 12) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 4
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | _ => 0

theorem acceptedPrefix_card_le_capacity (i : Fin 12) :
    (acceptedPrefix i).card ≤ capacityAt i := by
  fin_cases i
  · exact CFSGMathieuTwelvePrefixZeroCapacity.acceptedElements_card_le_one
  · exact CFSGMathieuTwelvePrefixOneCapacity.acceptedElements_card_le_whitelistLength
  · exact CFSGMathieuTwelvePrefixTwoCapacity.acceptedElements_card_le_whitelistLength
  · exact CFSGMathieuTwelvePrefixThreeCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixFourCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixFiveCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixSixCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixSevenCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixEightCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixNineCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixTenCapacity.acceptedElements_card_le_capacity
  · exact CFSGMathieuTwelvePrefixElevenCapacity.acceptedElements_card_le_capacity

theorem capacityAt_sum : (∑ i : Fin 12, capacityAt i) = 11 := by
  decide +kernel

theorem fixedAutomorphisms_card_le_eleven :
    Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement) ≤ 11 := by
  letI : Finite M12 := Finite.of_injective
    (fun g : M12 => (g : Perm12)) Subtype.val_injective
  have hcover : ∀ f : OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement,
      ∃ i : Fin 12, f.val secondElement ∈ acceptedPrefix i := by
    intro f
    obtain ⟨c,hc⟩ := decode_surjective (f.val secondElement)
    refine ⟨c.1.1,?_⟩
    rw [←hc]
    apply accepts_decode_mem_acceptedPrefix c
    rw [hc]
    exact accepts_of_fixed_first f.val f.property
  have h := FiniteIndexedAutomorphismImageCapacity.fixedAutomorphisms_card_le_sum
    secondElement firstElement fixed_pair_generates acceptedPrefix hcover
  have hs : (∑ i : Fin 12, (acceptedPrefix i).card) ≤ 11 := by
    calc
      _ ≤ ∑ i : Fin 12, capacityAt i :=
        Finset.sum_le_sum (fun i _ => acceptedPrefix_card_le_capacity i)
      _ = 11 := capacityAt_sum
  exact h.trans hs

theorem fixedAutomorphisms_card_le_twenty_four :
    Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms firstElement) ≤ 24 :=
  fixedAutomorphisms_card_le_eleven.trans (by decide)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveAcceptedCodeCapacity
