import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedLiftPullback
import SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedA2DerivedMatrixWitness

/-! Actual original derived words in the adjacent A2 fixed subgroup.
Every parameter and conjugation image remains in the same integral-tensor
model; no full unitary-model recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
open CFSG.Models.Chevalley CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
open CFSGSerreFixedRootElements

theorem mul_skew_fixed (q : CFSG.PrimePower) (t a : q.Extension 2)
    (ht : t ^ q.order = -t) (ha : a ^ q.order = a) :
    (t * a) ^ q.order = -(t * a) := by
  rw [mul_pow, ht, ha, neg_mul]

theorem inv_skew (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) : (t⁻¹) ^ q.order = -(t⁻¹) := by
  rw [inv_pow, ht, inv_neg]

def deltaDerived (q : CFSG.PrimePower) (t : q.Extension 2) (ht : t ^ q.order = -t)
    (a : q.Extension 2) (ha : a ^ q.order = a) :
    commutator (OriginalFixedA 2 q) :=
  derivedCommutator A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)
    (highestFixed q (t * a) (mul_skew_fixed q t a ht ha))
    (oppositeFixed q t⁻¹ (inv_skew q t ht))

theorem deltaDerived_image (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) (a : q.Extension 2) (ha : a ^ q.order = a) :
    twistedDerivedAction 2 q (deltaDerived q t ht a ha) =
      naturalElementaryAction (q.Extension 2) 2 (delta (q.Extension 2) t a) := by
  change naturalAction (q.Extension 2) 2
    (derivedToModel A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)
      (derivedCommutator A (q.Extension 2) CFSG.Models.reverseNode (fun _ => q.order)
        (highestFixed q (t * a) (mul_skew_fixed q t a ht ha))
        (oppositeFixed q t⁻¹ (inv_skew q t ht)))) = _
  rw [derivedToModel_commutator]
  change naturalAction (q.Extension 2) 2
    ⁅elementaryToModel (q.Extension 2) (highest (q.Extension 2) (t * a)),
      elementaryToModel (q.Extension 2) (opposite (q.Extension 2) t⁻¹)⁆ = _
  rw [map_commutatorElement, elementaryToModel_action, elementaryToModel_action]
  exact (map_commutatorElement (naturalElementaryAction (q.Extension 2) 2)
    (highest (q.Extension 2) (t * a)) (opposite (q.Extension 2) t⁻¹)).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedA2HighestRootUnits
