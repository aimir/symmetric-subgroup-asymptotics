import SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443ElevenGenerators
import SymmetricSubgroupAsymptotics.CFSGYBinaryDerivedFrames
import SymmetricSubgroupAsymptotics.SylowTwoNormalizerOfOddOrderSolvability
import SymmetricSubgroupAsymptotics.DerivedCenterSandwichEquivalence

/-! Actual facts for the new raw-derived Y443 carrier. The relation-set
transport below compares literal presentations; it does not change the
old Index.Model and says nothing about its Y555-centralizer Monster.
Binary generation and parity need no classification or source finiteness.
The GoodSylow corollary uses only odd-order solvability; the actual upstream
FeitThompson theorem supplies this on the common Axiom69 toolchain. It does
not require the old classification or an old/new Monster identification.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443BinaryFacts
open CFSG.Models.YGroups
open CFSGAxiomMonsterY443ElevenGenerators

def arms443 : Arms := ⟨monsterY443ArmLength,by intro i; fin_cases i <;> decide⟩

theorem adjacent_iff (i j : MonsterY443Gen) :
    MonsterY443Adj i j ↔ Adjacent arms443 i j := by
  cases i with
  | none => cases j <;> rfl
  | some q =>
    rcases q with ⟨i,d⟩
    cases j with
    | none => rfl
    | some q => rcases q with ⟨j,e⟩; rfl

theorem spider_eq : monsterY443SpiderWord=spider arms443 := rfl

theorem relations_eq : monsterY443Rels=relations arms443 := by
  ext w
  simp only [monsterY443Rels,relations,Set.mem_union,Set.mem_setOf_eq,Set.mem_singleton_iff]
  constructor
  · rintro (((hs | ha) | hn) | hsp)
    · exact Or.inl hs
    · obtain ⟨i,j,hij,hw⟩ := ha
      have hne : i≠j := by
        intro he
        subst j
        exact CFSGGeneration.y_adjacent_irrefl arms443 i ((adjacent_iff i i).mp hij)
      exact Or.inr (Or.inl ⟨i,j,hne,(adjacent_iff i j).mp hij,hw⟩)
    · obtain ⟨i,j,hne,hij,hw⟩ := hn
      exact Or.inr (Or.inr (Or.inl ⟨i,j,hne,fun h => hij ((adjacent_iff i j).mpr h),hw⟩))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [spider_eq] using hsp)))
  · rintro (hs | ha | hn | hsp)
    · exact Or.inl (Or.inl (Or.inl hs))
    · obtain ⟨i,j,hne,hij,hw⟩ := ha
      exact Or.inl (Or.inl (Or.inr ⟨i,j,(adjacent_iff i j).mpr hij,hw⟩))
    · obtain ⟨i,j,hne,hij,hw⟩ := hn
      exact Or.inl (Or.inr ⟨i,j,hne,fun h => hij ((adjacent_iff i j).mp h),hw⟩)
    · exact Or.inr (by simpa only [spider_eq] using hsp)

def rawMulEquiv : MonsterY443 ≃* CFSG.Models.YGroups.Group arms443 := by
  change PresentedGroup monsterY443Rels ≃* PresentedGroup (relations arms443)
  rw [relations_eq]
  exact MulEquiv.refl _

def derivedMulEquiv : MonsterY443Derived ≃*
    commutator (CFSG.Models.YGroups.Group arms443) :=
  DerivedCenterSandwichEquivalence.derivedEquiv
    (G := MonsterY443) (H := CFSG.Models.YGroups.Group arms443) rawMulEquiv

theorem exists_binary_generating_subgroups :
    ∃ U V : Subgroup MonsterY443Derived,IsPGroup 2 U ∧ IsPGroup 2 V ∧ U⊔V=⊤ := by
  obtain ⟨U,V,hU,hV,hgen⟩ := CFSGYBinaryDerivedFrames.exists_binary_generating_subgroups arms443
  let f := derivedMulEquiv.symm.toMonoidHom
  refine ⟨U.map f,V.map f,hU.map f,hV.map f,?_⟩
  rw [←Subgroup.map_sup,hgen,Subgroup.map_top_of_surjective f derivedMulEquiv.symm.surjective]

/-- In particular this applies to any actual native carrier reached by a
proved surjection, without requiring source finiteness. -/
theorem quotient_binary_generating_subgroups {H : Type} [Group H]
    (q : MonsterY443Derived →* H) (hq : Function.Surjective q) :
    ∃ U V : Subgroup H,IsPGroup 2 U ∧ IsPGroup 2 V ∧ U⊔V=⊤ := by
  obtain ⟨U,V,hU,hV,hgen⟩ := exists_binary_generating_subgroups
  refine ⟨U.map q,V.map q,hU.map q,hV.map q,?_⟩
  rw [←Subgroup.map_sup,hgen,Subgroup.map_top_of_surjective q hq]

theorem quotient_eleven_generators {H : Type} [Group H]
    (q : MonsterY443Derived →* H) (hq : Function.Surjective q) :
    ∃ S : Finset H,Subgroup.closure (S : Set H)=⊤ ∧ S.card≤11 :=
  CFSGGeneration.generators_card_le_of_surjective q hq derived_generators

theorem even_card (hn : ¬IsMulCommutative MonsterY443Derived) :
    Even (Nat.card MonsterY443Derived) := by
  apply CFSGReduction.even_card_of_derived_involution_quotient
    (PresentedGroup.of (rels := relations arms443)) none
    (PresentedGroup.closure_range_of (relations arms443))
    (fun i => by simpa only [pow_two] using CFSGGeneration.y_generator_sq arms443 i)
    (CFSGReduction.y_abelianization_generators_equal arms443)
    (CFSGReduction.yNonadjacent arms443)
    (CFSGReduction.y_nonadjacent_product_sq arms443)
    (CFSGReduction.y_nonadjacent_connected arms443)
    derivedMulEquiv.symm.toMonoidHom derivedMulEquiv.symm.surjective hn

theorem quotient_even_card {H : Type} [Group H]
    (q : MonsterY443Derived →* H) (hq : Function.Surjective q)
    (hn : ¬IsMulCommutative H) : Even (Nat.card H) := by
  exact CFSGReduction.even_card_of_derived_involution_quotient
    (PresentedGroup.of (rels := relations arms443)) none
    (PresentedGroup.closure_range_of (relations arms443))
    (fun i => by simpa only [pow_two] using CFSGGeneration.y_generator_sq arms443 i)
    (CFSGReduction.y_abelianization_generators_equal arms443)
    (CFSGReduction.yNonadjacent arms443)
    (CFSGReduction.y_nonadjacent_product_sq arms443)
    (CFSGReduction.y_nonadjacent_connected arms443)
    (q.comp derivedMulEquiv.symm.toMonoidHom)
    (hq.comp derivedMulEquiv.symm.surjective) hn

theorem goodSylowPrime [Finite MonsterY443Derived]
    (hodd : SylowTwoNormalizerOfOddOrderSolvability.OddOrderSolvability) :
    CFSGReduction.GoodSylowPrime MonsterY443Derived 2 := by
  obtain ⟨U,V,hU,hV,hgen⟩ := exists_binary_generating_subgroups
  exact SylowTwoNormalizerOfOddOrderSolvability.goodSylowTwo_of_two_binary_subgroups
    hodd U V hU hV hgen

theorem quotient_goodSylowPrime {H : Type} [Group H] [Finite H]
    (hodd : SylowTwoNormalizerOfOddOrderSolvability.OddOrderSolvability)
    (q : MonsterY443Derived →* H) (hq : Function.Surjective q) :
    CFSGReduction.GoodSylowPrime H 2 := by
  obtain ⟨U,V,hU,hV,hgen⟩ := quotient_binary_generating_subgroups q hq
  exact SylowTwoNormalizerOfOddOrderSolvability.goodSylowTwo_of_two_binary_subgroups
    hodd U V hU hV hgen

end SymmetricSubgroupAsymptotics.CFSGAxiomMonsterY443BinaryFacts
