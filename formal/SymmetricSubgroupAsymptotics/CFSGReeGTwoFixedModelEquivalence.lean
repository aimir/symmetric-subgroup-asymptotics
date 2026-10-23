import SymmetricSubgroupAsymptotics.CFSGSerreFixedModelEquivalence
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalGraph

/-! The complete original ReeG2 definition, including its actual derived
subgroup and full centre quotient, is equivalent to the same construction
inside the literal G2 Model fixed by the proved involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedModelEquivalence
open CFSG.Models.Chevalley CFSGReeGTwoFieldParameters
open CFSGReeGTwoOriginalAutomorphism CFSGSerreFixedModelEquivalence

abbrev originalModelFixed (m : ℕ) :=
  fixedModel CartanMatrix.G₂ (Field m) (reeAutomorphism m).toMonoidHom

def originalFixedEquiv (m : ℕ) :
    fixedSubgroup CartanMatrix.G₂ (Field m) CFSG.Models.reverseNode (originalExponent m) ≃*
      originalModelFixed m :=
  fixedModelEquiv CartanMatrix.G₂ (Field m) CFSG.Models.reverseNode (originalExponent m)
    (reeAutomorphism m).toMonoidHom (reeAutomorphism_root m)

def originalReeEquiv (m : ℕ) :
    CFSG.Models.ReeG2 m ≃* DerivedCentralQuotient (originalModelFixed m) :=
  twistedFixedModelEquiv CartanMatrix.G₂ (Field m) CFSG.Models.reverseNode (originalExponent m)
    (reeAutomorphism m).toMonoidHom (reeAutomorphism_root m)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedModelEquivalence
