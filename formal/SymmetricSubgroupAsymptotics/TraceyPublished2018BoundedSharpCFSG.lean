import SymmetricSubgroupAsymptotics.BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG
import SymmetricSubgroupAsymptotics.TraceyPublished2018PermutationBundle

/-! Fill only the bounded-sharp field of the published permutation bundle
from its actual CFSG proof. The coarse Tracey field remains explicit.
The existing bundle constructor retains the literal degree-three exception
and uses the already proved degree-at-least-22 and intransitive reductions.
No global sharp bound is assumed, and no additional published input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyPublished2018BoundedSharpCFSG

theorem boundedSharp_proved (hCFSG : CFSG.CFSGClassification) :
    TraceyPublished2018BoundedSharpPermutationInput := by
  intro n hlo hhi J ht
  exact BoundedSharpJankoTwoHeisenbergSingerCompleteCFSG.exists_generating_finset
    J hCFSG hlo (by omega) ht

def inputBundle_of_coarse (hCFSG : CFSG.CFSGClassification)
    (hTracey : TraceyPermutationGeneratorInput) : TraceyPublished2018PermutationInputBundle where
  coarse := hTracey
  boundedSharp := boundedSharp_proved hCFSG

theorem mcIverNeumann_of_coarse (hCFSG : CFSG.CFSGClassification)
    (hTracey : TraceyPermutationGeneratorInput) : McIverNeumannPermutationGeneratorBound :=
  (inputBundle_of_coarse hCFSG hTracey).mcIverNeumann

end SymmetricSubgroupAsymptotics.TraceyPublished2018BoundedSharpCFSG
