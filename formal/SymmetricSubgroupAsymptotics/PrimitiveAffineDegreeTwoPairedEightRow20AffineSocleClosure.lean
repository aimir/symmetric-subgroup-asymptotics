import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow20LinearNormalCertificate

/-!
# Closing the row-20 affine quotient-socle interface

The selected order-168 stabilizer certificate uses the same two literal
permutations as the affine coordinate model. Their pointwise equality
identifies the generated linear subgroups. Transporting the checked
simplicity theorem discharges the temporary affine-complement premise and
gives every normal quotient of the original row-20 top a two-position socle
witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPairedEightAffineTops

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

namespace Row20

/-- The selected stabilizer retains exactly the affine model's two literal
linear generators, with the same order and original point labels. -/
theorem selectedLinearGenerators_eq :
    PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.generators =
      linearTopGenerators := by
  funext i
  rw [linearTopGenerators_eq]
  fin_cases i <;> ext x <;> revert x <;> decide +kernel

theorem linearTop_eq_selectedClosure :
    linearTop = Subgroup.closure
      (Set.range
        PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.generators) := by
  change Subgroup.closure (Set.range linearTopGenerators) = _
  rw [selectedLinearGenerators_eq]

/-- Simplicity of the generated abstract linear complement follows from the
checked two-state normal registry of its literal permutation action. -/
theorem linearGroup_isSimpleGroup : IsSimpleGroup linearGroup := by
  letI : IsSimpleGroup
      (Subgroup.closure
        (Set.range
          PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.generators)) :=
    PrimitiveAffineDegreeTwoPairedEightRow20LinearNormalCertificate.literal_isSimpleGroup
  let e : linearGroup ≃* Subgroup.closure
      (Set.range
        PrimitiveAffineDegreeTwoPairedEightRow20LinearTopCertificate.generators) :=
    linearTopEquiv.trans (MulEquiv.subgroupCongr linearTop_eq_selectedClosure)
  exact e.isSimpleGroup

/-- The original literal row-20 group has the normal chain `1 < V < G`. -/
def normalChain : FiniteThreeNormalChainData Source := by
  letI : IsSimpleGroup linearGroup := linearGroup_isSimpleGroup
  exact normalChainOfSimple

/-- The row-20 simplicity premise is discharged by the selected certificate. -/
def topSocle (N : {N : Subgroup Source // N.Normal}) :
    SocleNormalGeneratorBound (Source ⧸ N.1) 2 := by
  letI : IsSimpleGroup linearGroup := linearGroup_isSimpleGroup
  exact topSocleOfSimple N

end Row20

/-- Closed quotient-socle export for the retained row-20 top. -/
def row20TopSocle :
    ∀ N : {N : Subgroup DegreeTwoPairedEightSharedTops.Top20 // N.Normal},
      SocleNormalGeneratorBound (DegreeTwoPairedEightSharedTops.Top20 ⧸ N.1) 2 :=
  Row20.topSocle

end PrimitiveAffineDegreeTwoPairedEightAffineTops
end SymmetricSubgroupAsymptotics

end
