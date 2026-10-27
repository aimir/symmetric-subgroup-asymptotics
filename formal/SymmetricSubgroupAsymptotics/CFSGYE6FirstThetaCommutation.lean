import SymmetricSubgroupAsymptotics.CFSGYE6FirstConjugationBraidPilot
import SymmetricSubgroupAsymptotics.CFSGYE6BraidCertificateConsumers

/-! The first already checked literal trace gives an actual theta
commutation, independently of how many proof chunks the producer used.
No additional model premise or finite certificate is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6FirstThetaCommutation
open CFSG.Models.YGroups CFSGYE6SelectedWords CFSGYE6BraidCertificateConsumers

private theorem first_identity (arms : Arms) :
    eval arms (guideW.reverse ++ [1] ++ guideW ++ [4])=1 := by
  rw [←CFSGYE6FirstConjugationBraidPilot.source_word]
  exact CFSGYE6FirstConjugationBraidPilot.selected_identity arms

theorem first_conjugation (arms : Arms) :
    (eval arms guideW)⁻¹*generator arms 1*eval arms guideW=generator arms 4 :=
  conjugation_of_identity arms 1 4 (first_identity arms)

theorem theta_commutes_first (arms : Arms) :
    Commute (generator arms 1) (eval arms thetaWord) :=
  theta_commutes_of_identity arms 1 4 rfl (first_identity arms)

end SymmetricSubgroupAsymptotics.CFSGYE6FirstThetaCommutation
