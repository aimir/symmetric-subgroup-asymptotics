import SymmetricSubgroupAsymptotics.Selected1542OriginalPreimageQuotientEquiv
import SymmetricSubgroupAsymptotics.Selected1542TargetCubicSurjective
import SymmetricSubgroupAsymptotics.QuotientRetainedHom

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

abbrev Quotient := Original ⧸ originalNormal

private theorem normal_le_target_kernel : originalNormal≤originalToTarget.ker := by
  rw [originalToTarget_ker]
  exact normal_le_preimage

def quotientToTarget : Quotient →* literalTarget :=
  QuotientRetainedHom.descend originalToTarget originalNormal normal_le_target_kernel

theorem quotientToTarget_apply (g : Original) :
    quotientToTarget (QuotientGroup.mk' originalNormal g)=originalToTarget g := rfl

theorem quotientToTarget_surjective : Function.Surjective quotientToTarget :=
  QuotientRetainedHom.descend_surjective originalToTarget originalNormal
    normal_le_target_kernel originalToTarget_surjective

theorem quotientToTarget_kernel : quotientToTarget.ker=
    originalPreimage.map (QuotientGroup.mk' originalNormal) := by
  rw [quotientToTarget,QuotientRetainedHom.descend_kernel,originalToTarget_ker]

def quotientAlternating : Quotient →* (Fin 2 → NaturalA4ScalarFourHead.G) :=
  targetAlternating.comp quotientToTarget

theorem quotientAlternating_kernel : quotientAlternating.ker=
    originalPreimage.map (QuotientGroup.mk' originalNormal) := by
  rw [←quotientToTarget_kernel]
  ext g
  change targetAlternating (quotientToTarget g)=1 ↔ quotientToTarget g=1
  exact map_eq_one_iff targetAlternating targetAlternating_injective

theorem quotientAlternating_common (g : Quotient) (i : Fin 2) :
    NaturalA4ScalarFourHead.top (quotientAlternating g i)=
      NaturalA4ScalarFourHead.top (quotientAlternating g 0) :=
  targetAlternating_common (quotientToTarget g) i

theorem quotient_top_surjective : Function.Surjective
    (ActualRepeatedAlternatingCentralCoordinates.top quotientAlternating 0) := by
  have htop : ActualRepeatedAlternatingCentralCoordinates.top quotientAlternating 0=
      (ActualRepeatedAlternatingCentralCoordinates.top targetAlternating 0).comp quotientToTarget := rfl
  rw [htop]
  exact target_top_surjective.comp quotientToTarget_surjective

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
