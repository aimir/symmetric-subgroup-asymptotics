import SymmetricSubgroupAsymptotics.RDTDegreeEightE8Action
import SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalTransport
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T1
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T2
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T3
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T4
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T5
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T6
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T7
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T8
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T9
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T10
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T11
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T15
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWordsPilot8T16
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T17
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T18
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T19
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T20
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T21
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T26
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T27
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T28
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T29
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T30
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T31
import SymmetricSubgroupAsymptotics.RDTDegreeEightNormalWords8T35

/-! Exact binary RDT degree-eight exception from the complete checked action
registry. Every nonexceptional original action has actual ambient normal
rank at most three; excess two supplies a normal requiring four seeds.
The remaining original action is the actual Heisenberg group E8. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalProof

open MarkedC4 MarkedC4.RDTExcessStructure
open RDTDegreeEightExceptionalTransport BinaryActionRegistry8

private theorem no_excess_of_normal_bound
    {G : Type} [Group G] [Finite G]
    (bound : ∀ (N : Subgroup G) [N.Normal], normalGen N ≤ 3) :
    ¬ HasExcess G 8 2 := by
  rintro ⟨⟨N,hN,hval⟩,_⟩
  letI : N.Normal := hN
  have hb : (normalGen N : ℝ) ≤ 3 := by exact_mod_cast bound N
  norm_num at hval
  linarith

/-- The checked normal-word bounds exclude all twenty-five other actual
registry actions. The finite index is not a catalogue classification input. -/
theorem index_eq_e8 (i : Fin 26) (hexcess : HasExcess (actions i) 8 2) :
    i = 18 := by
  by_contra hne
  fin_cases i
  · letI : Group (FiniteGroupRow 8) := BinaryMenuCayley8T1.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T1.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T1.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 8) := BinaryMenuCayley8T2.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T2.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T2.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 8) := BinaryMenuCayley8T3.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T3.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T3.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 8) := BinaryMenuCayley8T4.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T4.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T4.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 8) := BinaryMenuCayley8T5.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T5.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T5.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 16) := BinaryMenuCayley8T6.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T6.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T6.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 16) := BinaryMenuCayley8T7.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T7.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T7.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 16) := BinaryMenuCayley8T8.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T8.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T8.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 16) := BinaryMenuCayley8T9.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T9.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T9.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 16) := BinaryMenuCayley8T10.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T10.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T10.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 16) := BinaryMenuCayley8T11.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T11.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T11.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T15.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T15.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T15.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T16.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWordsPilot8T16.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T16.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T17.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T17.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T17.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T18.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T18.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T18.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T19.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T19.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T19.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T20.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T20.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T20.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 32) := BinaryMenuCayley8T21.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T21.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T21.originalEquiv.symm hexcess)
  · exact hne rfl
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T26.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T26.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T26.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T27.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T27.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T27.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T28.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T28.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T28.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T29.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T29.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T29.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T30.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T30.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T30.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T31.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T31.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T31.originalEquiv.symm hexcess)
  · letI : Group (FiniteGroupRow 128) := BinaryMenuCayley8T35.group
    exact no_excess_of_normal_bound RDTDegreeEightNormalWords8T35.all_normal_bound
      (hasExcess_of_equiv BinaryMenuCayley8T35.originalEquiv.symm hexcess)

/-- An excessive binary transitive eight-point source is the actual E8 group,
via the single point conjugation provided by checked action coverage. -/
theorem excessive_equiv_e8 (G : Subgroup (Equiv.Perm (Fin 8)))
    (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8, ∃ g : G, g.val x = y)
    (hexcess : HasExcess G 8 2) : Nonempty (G ≃* BinaryHeisenberg 2) := by
  have ht : PermutationSubgroupTransitive G := by
    intro x y
    obtain ⟨g,hg⟩ := htrans x y
    exact ⟨g.val,g.property,hg⟩
  obtain ⟨i,g,hg⟩ := BinaryActionRegistry8.complete G hG ht
  have hi : i = 18 := index_eq_e8 i
    (hasExcess_of_equiv (actionConjugacyEquiv g hg) hexcess)
  subst i
  exact ⟨(actionConjugacyEquiv g hg).trans RDTDegreeEightE8Action.modelEquiv.symm⟩

/-- Unconditional exact ordinary exceptional implication, on the original
source and every actual normal quotient. -/
theorem publishedDegreeEightExceptional :
    MarkedC4.RDTDegreeEightExceptional.PublishedDegreeEightExceptional := by
  intro n G hn hG htrans hexcess N hN hnonab
  subst n
  obtain ⟨e⟩ := excessive_equiv_e8 G hG htrans hexcess
  exact quotient_packet_of_equiv e RDTDegreeEightE8Structure.commutator_eq_center
    RDTDegreeEightE8Structure.commutator_card N hnonab

end SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalProof

end
