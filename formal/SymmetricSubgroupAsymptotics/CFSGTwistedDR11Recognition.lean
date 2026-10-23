import SymmetricSubgroupAsymptotics.CFSGTwistedDR11CommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGTwistedDDisjointCommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import Mathlib.Tactic.Linarith

/-! The actual fixed-field R11 relation is recognized by adjacency and
common-neighbour cardinality. Original rank four uses the genuine
nonsplit Witt-three bound one; higher ranks use (q+1)^2. There is no
split-D4 triality identification in this recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDR11Recognition
open CFSGTwistedDPlaneFamilyAction CFSGTwistedDPlaneAdjacencyActions
open CFSGTwistedDNormalizedCommonNeighbours CFSGTwistedDDisjointCommonNeighbours
open CFSGTwistedDR11CommonNeighbours CFSGTwistedDProjectiveUnipotent
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedA2FixedField

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

private theorem fourth_power_gt_bound (q : ℕ) (hq : 2 ≤ q) : (q + 1) ^ 2 < q ^ 4 := by
  have hm : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have hs : q + 1 < q ^ 2 := by nlinarith
  have h := Nat.pow_lt_pow_left hs (by decide : 2 ≠ 0)
  simpa only [← pow_mul] using h

theorem recognitionBound_lt_chart_size (s : ℕ) (q : CFSG.PrimePower) :
    recognitionBound s q < q.order ^ (2 * (s + 1)) := by
  have hq := CFSGTwistedAQuadraticTrace.order_two_le q
  by_cases hs : s = 0
  · subst s
    change 1 < q.order ^ 2
    nlinarith
  · calc
      recognitionBound s q = (q.order + 1) ^ 2 := by
        simp only [recognitionBound, if_neg hs]
      _ < q.order ^ 4 := fourth_power_gt_bound q.order hq
      _ ≤ q.order ^ (2 * (s + 1)) := Nat.pow_le_pow_right (by omega) (by omega)

theorem R11_iff_large_commonNeighbours (s : ℕ) (q : CFSG.PrimePower)
    (P Q : SingularPlanes s q) :
    IntersectingNonadjacent s q P Q ↔
      P ≠ Q ∧ ¬PlaneAdjacent s q P Q ∧
        recognitionBound s q < Nat.card (CommonNeighbours s q P Q) := by
  constructor
  · intro hr
    have hne : P ≠ Q := by
      intro he
      have hd := hr.1
      rw [he, inf_idem, Q.property.1] at hd
      omega
    exact ⟨hne, fun ha => hr.2 ha.2.2,
      (recognitionBound_lt_chart_size s q).trans_le (r11_commonNeighbours_card_lower s q P Q hr)⟩
  · rintro ⟨hne, hn, hc⟩
    rcases CFSGTwoPlaneIntersectionPartition.disjoint_or_inf_finrank_eq_one P.val Q.val
      P.property.1 Q.property.1 (fun he => hne (Subtype.ext he)) with hd | hi
    · exact False.elim ((Nat.not_lt_of_ge
        (disjoint_commonNeighbours_card_le_recognitionBound s q P Q hd)) hc)
    · exact ⟨hi, fun hs => hn ⟨hne, hi, hs⟩⟩

theorem adjacencyEquiv_preserves_R11 (s : ℕ) (q : CFSG.PrimePower)
    (f : Equiv.Perm (SingularPlanes s q))
    (hf : ∀ P Q, PlaneAdjacent s q (f P) (f Q) ↔ PlaneAdjacent s q P Q)
    (P Q : SingularPlanes s q) :
    IntersectingNonadjacent s q (f P) (f Q) ↔ IntersectingNonadjacent s q P Q := by
  have hc : Nat.card (CommonNeighbours s q (f P) (f Q)) = Nat.card (CommonNeighbours s q P Q) :=
    CFSGCommonNeighbourRecognition.commonNeighbour_card (PlaneAdjacent s q) f hf P Q
  rw [R11_iff_large_commonNeighbours, R11_iff_large_commonNeighbours, hc]
  exact and_congr (not_congr f.injective.eq_iff) (and_congr (not_congr (hf P Q)) Iff.rfl)

theorem singularAction_preserves_R11 (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (P Q : SingularPlanes s q) :
    IntersectingNonadjacent s q (singularActionHom s q f P) (singularActionHom s q f Q) ↔
      IntersectingNonadjacent s q P Q :=
  adjacencyEquiv_preserves_R11 s q (singularActionHom s q f)
    (singularAction_preserves_adjacency s q f) P Q

end SymmetricSubgroupAsymptotics.CFSGTwistedDR11Recognition
