import SymmetricSubgroupAsymptotics.CFSGAlternatingNormalizerProperLargeClass
import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowLargeClassSmallComplement

/-! Every actual normalizer transposition class of an alternating Sylow
two-subgroup in degree at least six has at most two points. The proof uses
the literal complement-size dichotomy and the two checked obstructions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingNormalizerSmallClasses
open Equiv CFSGNormalizerTranspositionClasses

theorem class_card_le_two {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (hn : 6 ≤ Nat.card X) (x : X) :
    (pointClass (Subgroup.normalizer
      (((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) : Set (Perm X))) x).ncard ≤ 2 := by
  let H := (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype
  let N := Subgroup.normalizer (H : Set (Perm X))
  let C := pointClass N x
  change C.ncard ≤ 2
  by_contra h
  have hlarge : 3 ≤ C.ncard := by omega
  by_cases hc : 2 ≤ Nat.card (Cᶜ : Set X)
  · exact CFSGAlternatingNormalizerProperLargeClass.impossible P x hlarge hc
  · have hsmall : (Cᶜ : Set X).ncard ≤ 1 := by
      have hcard : Nat.card (Cᶜ : Set X) ≤ 1 := by omega
      simpa only [Nat.card_coe_set_eq] using hcard
    exact CFSGAlternatingSylowLargeClassSmallComplement.impossible P hn x hsmall

end SymmetricSubgroupAsymptotics.CFSGAlternatingNormalizerSmallClasses
