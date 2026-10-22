import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularSubspaceAction
import SymmetricSubgroupAsymptotics.CFSGPolarSubspaceCardinality
import SymmetricSubgroupAsymptotics.CFSGSingularSubspaceDimensionBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveSubspace
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGramNondegenerate

/-! Actual B singular subspaces obey the original rank ceiling, and the
constructed group-automorphism action preserves their exact dimension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGPolarSubspacePoints
open CFSGOrthogonalBIntrinsicLongRoots CFSGOrthogonalBPositiveSubspace
variable {K : Type} [Field K] [Finite K]

theorem singularSubspace_finrank_le (h2 : (2 : K) ≠ 0) (n : ℕ)
    (W : Subspaces (gram K n).toBilin') : Module.finrank K W.val ≤ n := by
  have h := singular_two_finrank_le (gram K n).toBilin' (gram_nondegenerate h2 n) W
  have hd : Module.finrank K (Index n → K)=2*n+1 := by
    simp [Index,two_mul,add_assoc]
  omega

theorem singularSubspaceAction_finrank (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s+3)))
    (W : Subspaces (gram K (s+3)).toBilin') :
    Module.finrank K (singularSubspaceAction p h2 s f W).val=Module.finrank K W.val :=
  imageSubspace_finrank (gram K (s+3)).toBilin' (originalPointPermutationHom p h2 s f)
    (singularActionHom p h2 s f) (originalPointAction_incidence p h2 s f)
    (originalPointAction_preserves_orthogonal p h2 s f) W

def standardSingularSubspace (n : ℕ) : Subspaces (gram K n).toBilin' :=
  ⟨positiveSubspace K n,positiveSubspace_singular K n⟩

theorem standardSingularSubspace_finrank (n : ℕ) :
    Module.finrank K (standardSingularSubspace (K:=K) n).val=n := positiveSubspace_finrank K n

theorem full_rank_singular_maximal (h2 : (2 : K) ≠ 0) (n : ℕ)
    (W Z : Subspaces (gram K n).toBilin') (hW : Module.finrank K W.val=n)
    (hle : W.val ≤ Z.val) : W=Z :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_le hle
    ((singularSubspace_finrank_le h2 n Z).trans_eq hW.symm))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
