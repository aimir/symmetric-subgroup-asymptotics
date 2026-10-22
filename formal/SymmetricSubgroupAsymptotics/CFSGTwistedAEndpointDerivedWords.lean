import SymmetricSubgroupAsymptotics.CFSGTwistedAEndpointBlock
import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalImageKernel

/-! The same commutator word in the original fixed group, its natural
elementary lift, and the faithful first-coordinate block. Every equality
is on the literal original action image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley CFSGSerreSquareZeroMatrix CFSGTwistedAFirstBlock
open CFSGTwistedASLTwoDerivedWitness

def endpointNatural (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    NaturalElementary (q.Extension 2) (s + 3) :=
  elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) (s + 3))
    neg (endpointNode s) a *
  elementaryRoot (q.Extension 2) (naturalRootUnit (q.Extension 2) (s + 3))
    neg (endpointNode s).rev (a ^ q.order)

theorem endpointNatural_row_coe (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    (endpointNatural s q neg a).val = (pairedEndpointRowUnit s q neg a).val := rfl

theorem endpointFixed_action (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    twistedFixedAction (s + 3) q (endpointFixedRoot s q neg a) =
      naturalElementaryAction (q.Extension 2) (s + 3) (endpointNatural s q neg a) :=
  pairedFixedRoot_natural_action (s + 3) q neg (endpointNode s) (endpointNode_cartan_zero s) a

def endpointDerivedWord (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    commutator (fixedSubgroup (CartanMatrix.A (s + 3)) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order)) :=
  CFSGSerreFixedRootElements.derivedCommutator (CartanMatrix.A (s + 3)) (q.Extension 2)
    CFSG.Models.reverseNode (fun _ => q.order)
      (endpointFixedRoot s q false a) (endpointFixedRoot s q true 1)

def endpointDelta (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    NaturalElementary (q.Extension 2) (s + 3) :=
  ⁅endpointNatural s q false a, endpointNatural s q true 1⁆

def endpointDeltaRow (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    rowUnits (q.Extension 2) s :=
  ⁅pairedEndpointRowUnit s q false a, pairedEndpointRowUnit s q true 1⁆

theorem endpointDelta_row_coe (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    (endpointDelta s q a).val = (endpointDeltaRow s q a).val := rfl

theorem endpointDerivedWord_image (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    twistedDerivedAction (s + 3) q (endpointDerivedWord s q a) =
      naturalElementaryAction (q.Extension 2) (s + 3) (endpointDelta s q a) := by
  change twistedFixedAction (s + 3) q
    ⁅endpointFixedRoot s q false a, endpointFixedRoot s q true 1⁆ =
      naturalElementaryAction (q.Extension 2) (s + 3)
        ⁅endpointNatural s q false a, endpointNatural s q true 1⁆
  rw [map_commutatorElement, map_commutatorElement, endpointFixed_action, endpointFixed_action]

theorem endpointDeltaRow_block (s : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) :
    blockHom (q.Extension 2) s (endpointDeltaRow s q a) = deltaUnit a := by
  change blockHom (q.Extension 2) s
    ⁅pairedEndpointRowUnit s q false a, pairedEndpointRowUnit s q true 1⁆ = _
  rw [map_commutatorElement, pairedEndpointRowUnit_block, pairedEndpointRowUnit_block]
  change ⁅Matrix.SpecialLinearGroup.toGL (CFSGTypeASLTwoWeyl.upper a),
    Matrix.SpecialLinearGroup.toGL (CFSGTypeASLTwoWeyl.lower (1 : q.Extension 2))⁆ =
      Matrix.SpecialLinearGroup.toGL
        ⁅CFSGTypeASLTwoWeyl.upper a, CFSGTypeASLTwoWeyl.lower (1 : q.Extension 2)⁆
  exact (map_commutatorElement Matrix.SpecialLinearGroup.toGL _ _).symm

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
