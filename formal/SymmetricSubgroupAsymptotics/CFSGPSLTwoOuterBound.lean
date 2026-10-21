import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import SymmetricSubgroupAsymptotics.CFSGPSLTwoInnerTorus
import SymmetricSubgroupAsymptotics.CFSGPSLTwoTorusCardinality
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityAlignment
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters

/-! The literal PSL2 outer bound. The opposite-pair stabilizer embeds in
the square-scalar normalizer of its actual root group. Its size is at most
(q-1)f, while the same stabilizer contains the faithful actual inner torus
with q-1<=2|T|. Thus |Out(PSL2)|<=2f, including odd characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoOuterBound
open CFSGPSLTwoRootCoordinates CFSGPSLTwoGeometry CFSGPSLTwoPairRestriction
open CFSGOuterCardinalityAlignment PrimitiveSocleRawStructure
variable {F : Type} [Field F] [Finite F]

theorem outer_card_le : Nat.card (Outer (PSL (F:=F)))≤2*Nat.card (F ≃+* F) := by
  apply outer_card_le_of_aligned_bound (pairStabilizer (F:=F)) (pairTorus (F:=F))
    (d:=2*Nat.card (F ≃+* F))
  · intro f
    obtain ⟨g,hU,hO,_⟩ := exists_inner_fix_opposite_pair f
    exact ⟨g,hU,hO⟩
  · exact pairTorus_conj_mem_pair
  · exact inner_pairTorus_injective
  · calc
      Nat.card (pairStabilizer (F:=F))≤Nat.card Fˣ*Nat.card (F ≃+* F) := pairStabilizer_card_le
      _≤(2*Nat.card (pairTorus (F:=F)))*Nat.card (F ≃+* F) :=
        Nat.mul_le_mul_right _ card_units_le_two_mul_pairTorus
      _=Nat.card (pairTorus (F:=F))*(2*Nat.card (F ≃+* F)) := by ac_rfl

theorem typeA_rank_one_outer_card (q : CFSG.PrimePower) :
    Nat.card (Outer (CFSG.Models.A 1 q))≤2*q.exponent := by
  change Nat.card (Outer (PSL (F:=q.Field)))≤2*q.exponent
  simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
    (outer_card_le (F:=q.Field))

end SymmetricSubgroupAsymptotics.CFSGPSLTwoOuterBound
