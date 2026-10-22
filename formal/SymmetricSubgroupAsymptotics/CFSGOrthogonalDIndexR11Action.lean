import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAdjacencyAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Recognition
import SymmetricSubgroupAsymptotics.CFSGCommonNeighbourRecognition

/-! The proved R11 count criterion is bound to the SAME original
singular-plane carrier and its actual projective automorphism action.
This yields R11 preservation in ranks>=5, with no count hypothesis or
automorphism-lifting premise. Rank-four triality remains outside it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexResidualNeighborCount CFSGOrthogonalDIndexR11Recognition
variable (K : Type) [Field K]

abbrev CommonNeighbors (s : ℕ) (P Q : SingularPlanes K s) :=
  {R : SingularPlanes K s // QuadraticAdjacent K (s + 4) P.val R.val ∧
    QuadraticAdjacent K (s + 4) Q.val R.val}

def commonNeighborCarrierEquiv (s : ℕ) (P Q : SingularPlanes K s) :
    CommonNeighbors K s P Q ≃ CommonNeighborPlanes K (s + 4) P.val Q.val where
  toFun R := ⟨R.val.val, R.val.property.1, R.val.property.2, R.property⟩
  invFun R := ⟨⟨R.val, R.property.1, R.property.2.1⟩, R.property.2.2⟩
  left_inv R := Subtype.ext (Subtype.ext rfl)
  right_inv R := Subtype.ext rfl

theorem commonNeighbor_card_eq_flat (s : ℕ) (P Q : SingularPlanes K s) :
    Nat.card (CommonNeighbors K s P Q) = Nat.card (CommonNeighborPlanes K (s + 4) P.val Q.val) :=
  Nat.card_congr (commonNeighborCarrierEquiv K s P Q)

def IntersectingNonadjacent (s : ℕ) (P Q : SingularPlanes K s) : Prop :=
  Module.finrank K ↥(P.val ⊓ Q.val) = 1 ∧
    ¬∀ x ∈ P.val ⊔ Q.val, splitQuadraticForm K (s + 4) x = 0

theorem intersectingNonadjacent_iff_large_commonNeighbors [Finite K] (s : ℕ)
    (P Q : SingularPlanes K (s + 1)) :
    IntersectingNonadjacent K (s + 1) P Q ↔ P ≠ Q ∧
      ¬QuadraticAdjacent K (s + 5) P.val Q.val ∧
      (Nat.card K + 1) ^ 2 < Nat.card (CommonNeighbors K (s + 1) P Q) := by
  have h := R11_iff_large_common_neighbors K s P.val Q.val P.property.1 Q.property.1
    P.property.2 Q.property.2
  rw [← commonNeighbor_card_eq_flat K (s + 1) P Q] at h
  constructor
  · intro hr
    obtain ⟨hne, hn, hc⟩ := h.mp hr
    exact ⟨fun he => hne (congrArg Subtype.val he), hn, hc⟩
  · rintro ⟨hne, hn, hc⟩
    exact h.mpr ⟨fun he => hne (Subtype.ext he), hn, hc⟩

theorem adjacency_equiv_preserves_intersectingNonadjacent [Finite K] (s : ℕ)
    (f : SingularPlanes K (s + 1) ≃ SingularPlanes K (s + 1))
    (hf : ∀ P Q, QuadraticAdjacent K (s + 5) (f P).val (f Q).val ↔
      QuadraticAdjacent K (s + 5) P.val Q.val)
    (P Q : SingularPlanes K (s + 1)) :
    IntersectingNonadjacent K (s + 1) (f P) (f Q) ↔ IntersectingNonadjacent K (s + 1) P Q := by
  have hc : Nat.card (CommonNeighbors K (s + 1) (f P) (f Q)) =
      Nat.card (CommonNeighbors K (s + 1) P Q) :=
    CFSGCommonNeighbourRecognition.commonNeighbour_card
      (fun A B : SingularPlanes K (s + 1) => QuadraticAdjacent K (s + 5) A.val B.val) f hf P Q
  rw [intersectingNonadjacent_iff_large_commonNeighbors,
    intersectingNonadjacent_iff_large_commonNeighbors, hc]
  constructor
  · rintro ⟨hne, hn, hcard⟩
    exact ⟨fun he => hne (congrArg f he), fun ha => hn ((hf P Q).mpr ha), hcard⟩
  · rintro ⟨hne, hn, hcard⟩
    exact ⟨fun he => hne (f.injective he), fun ha => hn ((hf P Q).mp ha), hcard⟩

theorem singularAction_preserves_intersectingNonadjacent [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 5))) (P Q : SingularPlanes K (s + 1)) :
    IntersectingNonadjacent K (s + 1) (singularActionHom K p (s + 1) f P)
        (singularActionHom K p (s + 1) f Q) ↔ IntersectingNonadjacent K (s + 1) P Q :=
  adjacency_equiv_preserves_intersectingNonadjacent K s (singularActionHom K p (s + 1) f)
    (singularAction_preserves_adjacency K p (s + 1) f) P Q

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
