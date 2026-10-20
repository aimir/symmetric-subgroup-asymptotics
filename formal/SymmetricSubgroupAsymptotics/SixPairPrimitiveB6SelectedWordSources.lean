import SymmetricSubgroupAsymptotics.SixPairAction147PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction148PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction149PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction150PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction151PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction169PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction170PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction171PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction172PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction173PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction174PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction175PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction176PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction177PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction178PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction179PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction180PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction181PrimitiveB6Pilot
import SymmetricSubgroupAsymptotics.SixPairAction182PrimitiveB6Pilot

/-! All-normal B6 certificates for nineteen selected stored original actions.
Each generator tuple is literal. The common word theorem constructs its
primitive six-point module bound before inspecting any normal denominator.
This selected family does not supply the complete 182-action class locator.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairPrimitiveB6SelectedWordSources

def storedActionNumber : Fin 19 → ℕ := ![147,148,149,150,151,169,170,171,172,173,174,175,176,177,178,179,180,181,182]

def Original : Fin 19 → Subgroup (Equiv.Perm (Fin 12)) :=
  ![SixPairAction147PrimitiveB6Pilot.Original,
    SixPairAction148PrimitiveB6Pilot.Original,
    SixPairAction149PrimitiveB6Pilot.Original,
    SixPairAction150PrimitiveB6Pilot.Original,
    SixPairAction151PrimitiveB6Pilot.Original,
    SixPairAction169PrimitiveB6Pilot.Original,
    SixPairAction170PrimitiveB6Pilot.Original,
    SixPairAction171PrimitiveB6Pilot.Original,
    SixPairAction172PrimitiveB6Pilot.Original,
    SixPairAction173PrimitiveB6Pilot.Original,
    SixPairAction174PrimitiveB6Pilot.Original,
    SixPairAction175PrimitiveB6Pilot.Original,
    SixPairAction176PrimitiveB6Pilot.Original,
    SixPairAction177PrimitiveB6Pilot.Original,
    SixPairAction178PrimitiveB6Pilot.Original,
    SixPairAction179PrimitiveB6Pilot.Original,
    SixPairAction180PrimitiveB6Pilot.Original,
    SixPairAction181PrimitiveB6Pilot.Original,
    SixPairAction182PrimitiveB6Pilot.Original]

/-- Uniform complete certificate on every selected literal original group. -/
def actionCertificate (h6 : PublishedPrimitiveDegreeSixClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput) (j : Fin 19) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate (Original j) := by
  apply Classical.choice
  fin_cases j
  · exact ⟨SixPairAction147PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction148PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction149PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction150PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction151PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction169PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction170PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction171PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction172PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction173PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction174PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction175PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction176PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction177PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction178PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction179PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction180PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction181PrimitiveB6Pilot.actionCertificate h6 hZmud⟩
  · exact ⟨SixPairAction182PrimitiveB6Pilot.actionCertificate h6 hZmud⟩

end SymmetricSubgroupAsymptotics.SixPairPrimitiveB6SelectedWordSources
