import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4TwinQuotient
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexAdjacencyAction

/-! The stabilizer of the original root plane in the ACTUAL original
projective D4 automorphism action acts on the original neighbours and
preserves their true twins. No automorphism lift or triality action is
supplied as a hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexPlaneFamilyAction CFSGOrthogonalDIndexResidualNeighborCount
variable (K : Type) [Field K]

def originalRootPlane : SingularPlanes K 0 :=
  ⟨rootPlane K, rootPlane_finrank K, rootPlane_singular K⟩

def neighborAsPlane (S : Neighbors K) : SingularPlanes K 0 :=
  ⟨S.val, S.property.1, fun x hx => S.property.2.2 x (Submodule.mem_sup_right hx)⟩

theorem originalRoot_adjacent_neighbor (S : Neighbors K) :
    QuadraticAdjacent K 4 (originalRootPlane K).val (neighborAsPlane K S).val :=
  ⟨Ne.symm (neighbor_ne_rootPlane K S), S.property.2.1, S.property.2.2⟩

abbrev OriginalNeighborSubset := {P : SingularPlanes K 0 //
  QuadraticAdjacent K 4 (originalRootPlane K).val P.val}

def neighborSubsetEquiv : Neighbors K ≃ OriginalNeighborSubset K where
  toFun S := ⟨neighborAsPlane K S, originalRoot_adjacent_neighbor K S⟩
  invFun P := ⟨P.val.val, P.val.property.1, P.property.2.1, P.property.2.2⟩
  left_inv S := Subtype.ext rfl
  right_inv P := Subtype.ext (Subtype.ext rfl)

theorem neighbor_adjacent_iff_quadratic (S T : Neighbors K) :
    NeighborAdjacent K S T ↔ QuadraticAdjacent K 4 S.val T.val := by
  constructor
  · rintro ⟨hne, hi, hz⟩
    exact ⟨fun h => hne (Subtype.ext h), hi, hz⟩
  · rintro ⟨hne, hi, hz⟩
    exact ⟨fun h => hne (congrArg Subtype.val h), hi, hz⟩

variable [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
variable (f : MulAut (elementaryProjective K 4))
  (hfix : singularActionHom K p 0 f (originalRootPlane K) = originalRootPlane K)

def originalNeighborPermutation : Equiv.Perm (Neighbors K) :=
  (neighborSubsetEquiv K).trans
    ((Equiv.subtypeEquiv (singularActionHom K p 0 f) (fun P => by
      have hh := singularAction_preserves_adjacency K p 0 f (originalRootPlane K) P
      rw [hfix] at hh
      exact hh.symm)).trans (neighborSubsetEquiv K).symm)

theorem originalNeighborPermutation_preserves_adjacency (S T : Neighbors K) :
    NeighborAdjacent K (originalNeighborPermutation K p f hfix S)
      (originalNeighborPermutation K p f hfix T) ↔ NeighborAdjacent K S T := by
  rw [neighbor_adjacent_iff_quadratic, neighbor_adjacent_iff_quadratic]
  change QuadraticAdjacent K 4
    (singularActionHom K p 0 f (neighborAsPlane K S)).val
    (singularActionHom K p 0 f (neighborAsPlane K T)).val ↔ _
  exact singularAction_preserves_adjacency K p 0 f (neighborAsPlane K S) (neighborAsPlane K T)

theorem originalNeighborPermutation_preserves_closed (S T : Neighbors K) :
    ((originalNeighborPermutation K p f hfix S = originalNeighborPermutation K p f hfix T) ∨
      NeighborAdjacent K (originalNeighborPermutation K p f hfix S)
        (originalNeighborPermutation K p f hfix T)) ↔ (S = T ∨ NeighborAdjacent K S T) := by
  constructor
  · rintro (he | ha)
    · exact Or.inl ((originalNeighborPermutation K p f hfix).injective he)
    · exact Or.inr ((originalNeighborPermutation_preserves_adjacency K p f hfix S T).mp ha)
  · rintro (he | ha)
    · exact Or.inl (congrArg (originalNeighborPermutation K p f hfix) he)
    · exact Or.inr ((originalNeighborPermutation_preserves_adjacency K p f hfix S T).mpr ha)

theorem originalNeighborPermutation_preserves_twins (S T : Neighbors K) :
    NeighborTrueTwins K (originalNeighborPermutation K p f hfix S)
      (originalNeighborPermutation K p f hfix T) ↔ NeighborTrueTwins K S T := by
  let e := originalNeighborPermutation K p f hfix
  constructor
  · intro h V
    exact (originalNeighborPermutation_preserves_closed K p f hfix S V).symm.trans
      ((h (e V)).trans (originalNeighborPermutation_preserves_closed K p f hfix T V))
  · intro h V
    have hS := originalNeighborPermutation_preserves_closed K p f hfix S (e.symm V)
    have hT := originalNeighborPermutation_preserves_closed K p f hfix T (e.symm V)
    change (e S = e (e.symm V) ∨ NeighborAdjacent K (e S) (e (e.symm V))) ↔ _ at hS
    change (e T = e (e.symm V) ∨ NeighborAdjacent K (e T) (e (e.symm V))) ↔ _ at hT
    rw [e.apply_symm_apply] at hS hT
    exact hS.trans ((h (e.symm V)).trans hT.symm)

def originalTwinQuotientPermutation : Equiv.Perm (NeighborTwinQuotient K) :=
  Quotient.congr (originalNeighborPermutation K p f hfix)
    (fun S T => (originalNeighborPermutation_preserves_twins K p f hfix S T).symm)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
