import SymmetricSubgroupAsymptotics.CFSGTwistedDRootProductAdjacency

/-! Every actual projective automorphism preserves the original
fixed-field Q-singular plane adjacency graph. Distinctness is retained
explicitly because a root product inside one root line is not an edge. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneAdjacencyActions
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDIntrinsicRootProduct
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedDRootProductAdjacency
open CFSGTwistedA2FixedField

def PlaneAdjacent (s : ℕ) (q : CFSG.PrimePower) (P Q : SingularPlanes s q) : Prop :=
  P ≠ Q ∧
    Module.finrank (fixedField q)
      (P.val ⊓ Q.val : Submodule (fixedField q) (fixedSpace (s + 2) q)) = 1 ∧
    ∀ z ∈ P.val ⊔ Q.val, fixedQuadraticForm (s + 2) q z = 0

theorem adjacency_iff_distinct_rootProduct (s : ℕ) (q : CFSG.PrimePower)
    (P Q : SingularPlanes s q) :
    PlaneAdjacent s q P Q ↔ P ≠ Q ∧
      RootProductRelation s q (singularLabel s q P) (singularLabel s q Q) := by
  by_cases hne : P = Q
  · subst Q
    simp only [PlaneAdjacent, ne_eq, not_true_eq_false, false_and]
  have hnerep : conjugateRootPlane s q (representative s q P) ≠
      conjugateRootPlane s q (representative s q Q) := by
    intro he
    exact hne (Subtype.ext ((representative_spec s q P).trans
      (he.trans (representative_spec s q Q).symm)))
  have he := projective_root_product_adjacency_iff s q
    (representative s q P) (representative s q Q) hnerep
  rw [← representative_spec s q P, ← representative_spec s q Q] at he
  change (P ≠ Q ∧ _) ↔ P ≠ Q ∧ _
  exact and_congr_right (fun _ => he.symm)

theorem singularAction_preserves_adjacency (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (P Q : SingularPlanes s q) :
    PlaneAdjacent s q (singularActionHom s q f P) (singularActionHom s q f Q) ↔
      PlaneAdjacent s q P Q := by
  rw [adjacency_iff_distinct_rootProduct, adjacency_iff_distinct_rootProduct,
    singularAction_RootProductRelation_iff]
  exact and_congr
    (not_congr (singularActionHom s q f).injective.eq_iff) Iff.rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneAdjacencyActions
