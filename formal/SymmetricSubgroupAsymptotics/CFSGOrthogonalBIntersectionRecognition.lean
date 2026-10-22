import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneIntersectionPartition
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBDisjointCommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRankThreeCommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBAdjacencyActions
import SymmetricSubgroupAsymptotics.CFSGCommonNeighbourRecognition

/-! A thin actual-carrier recognition step. The disjoint alternatives
have already proved small bounds. The only input here is the explicit
remaining lower count on intersecting nonadjacent planes; this module
does not assert that lower count, polar point reconstruction, or an Out
bound. Rank three uses bound 1, all higher ranks use (q+1)^2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

def intersectionRecognitionBound (s : ℕ) : ℕ :=
  if s = 0 then 1 else (Nat.card K + 1) ^ 2

theorem disjoint_common_neighbours_card_le_recognitionBound (h2 : (2 : K) ≠ 0)
    (s : ℕ) (P Q : SingularPlanes (K := K) s) (hd : Disjoint P.val Q.val) :
    Nat.card (CommonNeighbours s P Q) ≤ intersectionRecognitionBound (K := K) s := by
  by_cases hs : s = 0
  · subst s
    simpa only [intersectionRecognitionBound, if_pos rfl] using
      rank_three_disjoint_common_neighbours_card_le_one h2 P Q hd
  · simpa only [intersectionRecognitionBound, if_neg hs] using
      disjoint_common_neighbours_card_le s P Q hd

theorem intersectingNonadjacent_iff_large_commonNeighbours (h2 : (2 : K) ≠ 0)
    (s : ℕ)
    (hlarge : ∀ P Q : SingularPlanes (K := K) s, IntersectingNonadjacent s P Q →
      intersectionRecognitionBound (K := K) s < Nat.card (CommonNeighbours s P Q))
    (P Q : SingularPlanes (K := K) s) :
    IntersectingNonadjacent s P Q ↔ P ≠ Q ∧ ¬PlaneAdjacent s P.val Q.val ∧
      intersectionRecognitionBound (K := K) s < Nat.card (CommonNeighbours s P Q) := by
  constructor
  · intro h
    exact ⟨intersectingNonadjacent_ne s P Q h,
      intersectingNonadjacent_not_adjacent s P Q h, hlarge P Q h⟩
  · rintro ⟨hne, hn, hc⟩
    rcases distinct_nonadjacent_partition s P Q hne hn with hd | hi
    · exact False.elim ((Nat.not_lt_of_ge
        (disjoint_common_neighbours_card_le_recognitionBound h2 s P Q hd)) hc)
    · exact hi

theorem adjacency_equiv_preserves_intersectingNonadjacent (h2 : (2 : K) ≠ 0)
    (s : ℕ)
    (hlarge : ∀ P Q : SingularPlanes (K := K) s, IntersectingNonadjacent s P Q →
      intersectionRecognitionBound (K := K) s < Nat.card (CommonNeighbours s P Q))
    (f : SingularPlanes (K := K) s ≃ SingularPlanes (K := K) s)
    (hf : ∀ P Q, PlaneAdjacent s (f P).val (f Q).val ↔ PlaneAdjacent s P.val Q.val)
    (P Q : SingularPlanes (K := K) s) :
    IntersectingNonadjacent s (f P) (f Q) ↔ IntersectingNonadjacent s P Q := by
  have hc : Nat.card (CommonNeighbours s (f P) (f Q)) = Nat.card (CommonNeighbours s P Q) :=
    CFSGCommonNeighbourRecognition.commonNeighbour_card
      (fun A B : SingularPlanes (K := K) s => PlaneAdjacent s A.val B.val) f hf P Q
  rw [intersectingNonadjacent_iff_large_commonNeighbours h2 s hlarge,
    intersectingNonadjacent_iff_large_commonNeighbours h2 s hlarge, hc]
  constructor
  · rintro ⟨hne, hn, hcard⟩
    exact ⟨fun he => hne (congrArg f he), fun ha => hn ((hf P Q).mpr ha), hcard⟩
  · rintro ⟨hne, hn, hcard⟩
    exact ⟨fun he => hne (f.injective he), fun ha => hn ((hf P Q).mp ha), hcard⟩

theorem singularAction_preserves_intersectingNonadjacent (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ)
    (hlarge : ∀ P Q : SingularPlanes (K := K) s, IntersectingNonadjacent s P Q →
      intersectionRecognitionBound (K := K) s < Nat.card (CommonNeighbours s P Q))
    (f : MulAut (elementaryProjective K (s + 3))) (P Q : SingularPlanes (K := K) s) :
    IntersectingNonadjacent s (singularActionHom p h2 s f P) (singularActionHom p h2 s f Q) ↔
      IntersectingNonadjacent s P Q :=
  adjacency_equiv_preserves_intersectingNonadjacent h2 s hlarge
    (singularActionHom p h2 s f) (singularAction_preserves_adjacency p h2 s f) P Q

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
