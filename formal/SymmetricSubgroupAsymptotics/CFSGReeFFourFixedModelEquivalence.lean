import SymmetricSubgroupAsymptotics.CFSGSerreFixedModelEquivalence
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalGraph

/-! Exact transport of the ORIGINAL ReeF4 and Tits definitions into the
same original F4 Model fixed by the proved involution. The actual derived
subgroup and its FULL centre quotient are preserved, including at m=0.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedModelEquivalence
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGSerreFixedModelEquivalence

abbrev originalModelFixed (m:ℕ):=
  fixedModel CartanMatrix.F₄ (Field m) (reeAutomorphism m).toMonoidHom

def originalFixedEquiv (m:ℕ):
    fixedSubgroup CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)≃*
      originalModelFixed m:=
  fixedModelEquiv CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)
    (reeAutomorphism m).toMonoidHom (reeAutomorphism_root m)

def originalReeEquiv (m:ℕ):
    CFSG.Models.ReeF4 m≃*DerivedCentralQuotient (originalModelFixed m):=
  twistedFixedModelEquiv CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)
    (reeAutomorphism m).toMonoidHom (reeAutomorphism_root m)

def originalTitsEquiv:
    CFSG.Models.Tits≃*DerivedCentralQuotient (originalModelFixed 0):=originalReeEquiv 0

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedModelEquivalence
