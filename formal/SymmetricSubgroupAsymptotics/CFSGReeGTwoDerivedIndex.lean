import SymmetricSubgroupAsymptotics.CFSGTwoCellDerivedIndex
import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedCenter
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareIndex

/-! The full fixed group need not be assumed perfect: its actual derived
subgroup has index at most four. Squared torus words are commutators and
the two actual Bruhat cells cover its abelian quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedIndex
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoOriginalTorus CFSGReeGTwoOriginalOpposition CFSGReeGTwoOppositionTorus
open CFSGReeGTwoFixedFactorDescent CFSGReeGTwoFixedCardinalitySylow
open CFSGReeGTwoPositiveDerived CFSGReeGTwoDerivedCenter
attribute [local instance] fixedModel_finite

theorem fixed_derived_index_le_four (m : ℕ) (hm : 1≤m) :
    (commutator (originalModelFixed m)).index≤4 :=
  CFSGTwoCellDerivedIndex.derived_index_le_four
    (borelGroup m) (fixedPositiveGroup m) (fixedOpposition m) (fixedTorusHom m)
    (fixedPositiveGroup_le_commutator m hm) (fixedTorus_square_mem_commutator m)
    (CFSGFiniteFieldSquareIndex.squares_index_le_two (Field m))
    (by rintro _ ⟨x,rfl⟩; exact ⟨x.left.val,x.left.property,x.right,borelHom_apply m x⟩)
    (fixed_bruhat m)

theorem fixed_card_le_four_mul_derived (m : ℕ) (hm : 1≤m) :
    Nat.card (originalModelFixed m)≤4*Nat.card (commutator (originalModelFixed m)) := by
  rw [←(commutator (originalModelFixed m)).card_mul_index]
  exact (Nat.mul_le_mul_left (Nat.card (commutator (originalModelFixed m)))
    (fixed_derived_index_le_four m hm)).trans_eq (Nat.mul_comm _ _)

theorem original_order_lower (m : ℕ) (hm : 1≤m) :
    (3^(2*m+1))^3*(3^(2*m+1)-1)*((3^(2*m+1))^3+1)≤
      4*Nat.card (CFSG.Models.ReeG2 m) := by
  have hc : Nat.card (CFSG.Models.ReeG2 m)=Nat.card (commutator (originalModelFixed m)) :=
    Nat.card_congr (originalReeEquivDerived m hm).toEquiv
  rw [hc,←fixed_group_card]
  exact fixed_card_le_four_mul_derived m hm

end SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedIndex
