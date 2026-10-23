import SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedCentreFaithful
import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedTorusCard
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityAlignment
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The actual opposed-pair stabilizer embeds into the central-axis
scalar normalizer. Charging the same actual inner derived torus cancels
the field-unit factor, leaving at most twice the original field degree.
Every group and equivalence here is the pinned original Ree model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOuterBound
open PrimitiveSocleRawStructure CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoPairRestriction CFSGReeGTwoAlignedAutomorphisms
open CFSGReeGTwoAlignedCentreFaithful CFSGReeGTwoDerivedTorusCard CFSGReeGTwoDerivedPairNormalizer
open CFSGReeGTwoDerivedCenter CFSGReeGTwoFixedCardinalitySylow CFSGOuterCardinalityAlignment
attribute [local instance] fixedModel_finite

theorem derived_outer_card_le_field (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] :
    Nat.card (Outer (commutator (originalModelFixed m)))≤2*Nat.card (Field m≃+*Field m) := by
  apply outer_card_le_of_aligned_bound (pairStabilizer m hm) (derivedTorus m)
    (d:=2*Nat.card (Field m≃+*Field m))
  · intro f
    obtain ⟨g,hU,hO,_⟩ := exists_inner_preserve_U_opposite_torus m hm f
    refine ⟨g,?_⟩
    intro neg
    cases neg
    · exact hU
    · exact hO
  · exact inner_derivedTorus_mem_pair m hm
  · exact inner_derivedTorus_injective m hm
  · calc
      Nat.card (pairStabilizer m hm)≤Nat.card (Field m)ˣ*Nat.card (Field m≃+*Field m) :=
        pairStabilizer_card_le m hm
      _≤(2*Nat.card (derivedTorus m))*Nat.card (Field m≃+*Field m) :=
        Nat.mul_le_mul_right _ (units_card_le_twice_derivedTorus m)
      _=Nat.card (derivedTorus m)*(2*Nat.card (Field m≃+*Field m)) := by ring

theorem original_outer_card_le_field (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] :
    Nat.card (Outer (CFSG.Models.ReeG2 m))≤2*Nat.card (Field m≃+*Field m) := by
  rw [CFSGReduction.outer_card_congr (originalReeEquivDerived m hm)]
  exact derived_outer_card_le_field m hm

theorem outer_card_le (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] :
    Nat.card (Outer (CFSG.Models.ReeG2 m))≤2*(2*m+1) := by
  have hfield : Nat.card (Field m≃+*Field m)=2*m+1 :=
    CFSGFiniteFieldAutomorphisms.card_galoisField_ringAut 3 (2*m+1) (by omega)
  exact (original_outer_card_le_field m hm).trans_eq (congrArg (fun n:ℕ=>2*n) hfield)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalOuterBound
