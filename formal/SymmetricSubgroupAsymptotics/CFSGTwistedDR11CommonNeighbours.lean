import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePlaneTransport
import SymmetricSubgroupAsymptotics.CFSGTwistedDR11Frame

/-! The explicit residual chart gives a uniform actual R11 lower count
in every original rank at least four. In rank four it already supplies
q^2 common neighbours, so no split-D4 triality claim enters the count. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDR11CommonNeighbours
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDPlaneAdjacencyActions
open CFSGTwistedDNormalizedCommonNeighbours CFSGTwistedDRelativePlaneTransport
open CFSGTwistedDR11Frame CFSGTwistedA2FixedField

def IntersectingNonadjacent (s : ℕ) (q : CFSG.PrimePower) (P Q : SingularPlanes s q) : Prop :=
  Module.finrank (fixedField q)
    (P.val ⊓ Q.val : Submodule (fixedField q) (fixedSpace (s + 2) q)) = 1 ∧
    ¬∀ x ∈ P.val ⊔ Q.val, fixedQuadraticForm (s + 2) q x = 0

theorem r11_commonNeighbours_card_lower (s : ℕ) (q : CFSG.PrimePower)
    (P Q : SingularPlanes s q) (hr : IntersectingNonadjacent s q P Q) :
    q.order ^ (2 * (s + 1)) ≤ Nat.card (CommonNeighbours s q P Q) := by
  have hmeet : (P.val ⊓ Q.val :
      Submodule (fixedField q) (fixedSpace (s + 2) q)) ≠ ⊥ := by
    intro he
    have hz := congrArg
      (fun T : Submodule (fixedField q) (fixedSpace (s + 2) q) => Module.finrank (fixedField q) T) he
    dsimp only at hz
    rw [finrank_bot, hr.1] at hz
    omega
  obtain ⟨g, w, hP, hQ, hws, hwu, hw⟩ := exists_normalized_frame s q P.val Q.val
    P.property.1 Q.property.1 P.property.2 Q.property.2 hmeet hr.2
  have hPa : singularActionHom s q (MulAut.conj (projection s q g)) P = standardPlane s q := by
    apply Subtype.ext
    exact (innerPlane_action_map s q g P).trans hP
  have hQa : singularActionHom s q (MulAut.conj (projection s q g)) Q =
      companionPlane s q w hws hwu hw := by
    apply Subtype.ext
    exact (innerPlane_action_map s q g Q).trans hQ
  have hc := inner_commonNeighbours_card s q g P Q
  rw [hPa, hQa] at hc
  exact (normalized_commonNeighbours_card_lower s q w hws hwu hw).trans_eq hc

end SymmetricSubgroupAsymptotics.CFSGTwistedDR11CommonNeighbours
