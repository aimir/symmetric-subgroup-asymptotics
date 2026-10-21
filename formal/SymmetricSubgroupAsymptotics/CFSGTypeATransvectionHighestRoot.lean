import SymmetricSubgroupAsymptotics.CFSGTypeALinearConjugation
import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionBasis
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryMatrices
import Mathlib.Data.Matrix.Basis

/-! Every nonidentity original SL transvection is carried to the literal
highest-root matrix by a proved linear-conjugation automorphism. This is
an unrestricted original change of basis, not an unproved inner-conjugacy
claim or abstract classical-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionHighestRoot
open Matrix Module LinearMap CFSGTypeAProjectivePointRoots CFSGTypeAElementaryMatrices
variable {F : Type*} [Field F]

theorem elementary_apply {I : Type*} [Fintype I] [DecidableEq I]
    {i j : I} (hij : i≠j) (a : F) (x : I→F) :
    (elementary hij a).toLin' x=x+(a*x j) • Pi.single i 1 := by
  change Matrix.transvection i j a *ᵥ x=_
  rw [Matrix.transvection,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec]
  ext k
  by_cases hk : k=i <;>
    simp [Function.update_apply,Pi.single_apply,hk,eq_comm]

theorem exists_linearConjugation_highestRoot {n : ℕ} (hn : 2≤n)
    (f : Dual F (Fin n→F)) (v : Fin n→F) (hfv : f v=0) (hf : f≠0) (hv : v≠0) :
    ∃e : (Fin n→F)≃ₗ[F](Fin n→F),
      linearConjugation e (transvectionSL hfv)=
        elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
          intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) (1 : F) := by
  obtain ⟨e,hev,hef⟩ := CFSGTypeATransvectionBasis.exists_highest_root_coordinates hn f v hfv hf hv
  refine ⟨e,?_⟩
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro x
  rw [linearConjugation_apply,transvectionSL_apply,elementary_apply]
  rw [map_add,map_smul,e.apply_symm_apply,hev,hef,one_mul]

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionHighestRoot
