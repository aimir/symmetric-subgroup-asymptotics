import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootRelation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborCount

/-! Every automorphism of the SAME projective D quotient preserves
the exact adjacency of ALL original Q-singular two-planes, in every
characteristic and rank>=4. This uses the intrinsic root-product test;
it does not distinguish the D4 triality-related point types. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneRootLine
open CFSGOrthogonalDIndexProjectiveUnipotent CFSGOrthogonalDIndexProjectiveRootFamily
open CFSGOrthogonalDIndexProjectiveRootAdjacency CFSGOrthogonalDIndexResidualNeighborCount
variable (K : Type) [Field K]

theorem root_relation_labels_iff_adjacency (s : ℕ) (P Q : SingularPlanes K s) (hne : P ≠ Q) :
    RootProductRelation K s (singularLabel K s P) (singularLabel K s Q) ↔
      QuadraticAdjacent K (s + 4) P.val Q.val := by
  have hneval : P.val ≠ Q.val := fun he => hne (Subtype.ext he)
  have hne' : conjugateRootPlane K s (representative K s P) ≠
      conjugateRootPlane K s (representative K s Q) := by
    rw [← representative_spec K s P, ← representative_spec K s Q]
    exact hneval
  have h := projective_root_product_adjacency_iff K s (representative K s P) (representative K s Q) hne'
  change RootProductRelation K s (singularLabel K s P) (singularLabel K s Q) ↔ _ at h
  rw [← representative_spec K s P, ← representative_spec K s Q] at h
  constructor
  · intro hr
    exact ⟨hneval, h.mp hr⟩
  · intro ha
    exact h.mpr ha.2

theorem singularAction_preserves_adjacency [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4))) (P Q : SingularPlanes K s) :
    QuadraticAdjacent K (s + 4) (singularActionHom K p s f P).val (singularActionHom K p s f Q).val ↔
      QuadraticAdjacent K (s + 4) P.val Q.val := by
  by_cases he : P = Q
  · subst Q
    constructor <;> intro h <;> exact False.elim (h.1 rfl)
  · have hne : singularActionHom K p s f P ≠ singularActionHom K p s f Q :=
      fun h => he ((singularActionHom K p s f).injective h)
    calc
      _ ↔ RootProductRelation K s (singularLabel K s (singularActionHom K p s f P))
          (singularLabel K s (singularActionHom K p s f Q)) :=
        (root_relation_labels_iff_adjacency K s _ _ hne).symm
      _ ↔ RootProductRelation K s ((singularLabel K s P).map f.toMonoidHom)
          ((singularLabel K s Q).map f.toMonoidHom) := by rw [singularLabel_action, singularLabel_action]
      _ ↔ RootProductRelation K s (singularLabel K s P) (singularLabel K s Q) :=
        automorphism_RootProductRelation_iff K p s f _ _
      _ ↔ QuadraticAdjacent K (s + 4) P.val Q.val := root_relation_labels_iff_adjacency K s P Q he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
