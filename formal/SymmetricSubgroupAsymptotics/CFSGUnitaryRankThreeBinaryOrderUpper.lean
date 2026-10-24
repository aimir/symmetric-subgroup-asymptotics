import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryFourIsotropicCardinality
import SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryOrderUpper
import SymmetricSubgroupAsymptotics.CFSGHermitianFirstOrbitOrderBound

/-! A first-column isotropic carrier sharpens the same original binary
rank-three unitary order bound. All later columns use the preserved
pairing-prefix fibres; no exact classical order formula is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists
open CFSGHermitianIsometryOrderBound

theorem naturalFixed_binary_four_card_le (q : CFSG.PrimePower) (hq : q.order=2) :
    Nat.card (naturalFixed 3 q) ≤ 655360 := by
  let rho : naturalFixed 3 q →* (Mat (q.Extension 2) 3)ˣ :=
    (NaturalElementary (q.Extension 2) 3).subtype.comp (naturalFixed 3 q).subtype
  have hinj : Function.Injective rho :=
    (NaturalElementary (q.Extension 2) 3).subtype_injective.comp
      (naturalFixed 3 q).subtype_injective
  have hS (g : naturalFixed 3 q) :
      (rho g).val *ᵥ Pi.single (0:Fin 4) 1 ∈ unitaryIsotropicVectors q 3 := by
    change unitaryNaturalPair q 3
      ((g.val.val : Mat (q.Extension 2) 3) *ᵥ Pi.single (0:Fin 4) 1)
      ((g.val.val : Mat (q.Extension 2) 3) *ᵥ Pi.single (0:Fin 4) 1) = 0
    rw [natural_unitary_pair_preserved,unitaryNaturalPair_first]
    simp only [Pi.single_apply,show (Fin.last 3 : Fin 4) ≠ 0 by decide,if_false]
  have h := card_le_pairing_first_carrier rho hinj (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 3) (fun g => naturalFixed_signedForm q 3 g)
    (unitaryIsotropicVectors q 3) hS
  have hh := h.trans (Nat.mul_le_mul_right _
    (unitaryIsotropicVectors_binary_four_card_le q hq))
  simpa only [extension_two_card,hq,Nat.reduceAdd,Nat.reduceMul,Nat.reduceDiv,
    Nat.reducePow] using hh

theorem twistedA_rankThree_binary_order_le (q : CFSG.PrimePower) (hq : q.order=2) :
    Nat.card (CFSG.Models.TwistedA 3 q) ≤ 655360 :=
  (Nat.card_le_card_of_surjective (unitaryProjectiveCover q 0)
    (unitaryProjectiveCover_surjective q 0)).trans
      (naturalFixed_binary_four_card_le q hq)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
