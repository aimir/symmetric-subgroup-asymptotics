import SymmetricSubgroupAsymptotics.CFSGExceptionalDiagramAutomorphisms
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Equiv.Basic

/-! The actual permutation-linear image of a Cartan diagram group. An
integral linear map sending every simple vector to its diagram permutation
belongs to this soluble image whenever the original diagram group is soluble. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction
open CFSGExceptionalDiagramAutomorphisms
variable {I : Type*} [Fintype I] [DecidableEq I]

def permutationLinear : Equiv.Perm I→*((I→ℤ)≃ₗ[ℤ](I→ℤ)) where
  toFun := fun σ=>LinearEquiv.funCongrLeft ℤ ℤ σ.symm
  map_one' := by
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' := by
    intro σ τ
    apply LinearEquiv.ext
    intro x
    funext j
    change x ((σ*τ)⁻¹ j)=x ((τ⁻¹*σ⁻¹) j)
    rw [mul_inv_rev]

theorem permutationLinear_single (σ : Equiv.Perm I) (i : I) :
    permutationLinear σ (Pi.single i 1)=Pi.single (σ i) 1 := by
  funext j
  change (Pi.single i (1:ℤ) : I→ℤ) (σ.symm j)=
    (Pi.single (σ i) (1:ℤ) : I→ℤ) j
  by_cases hj : j=σ i
  · subst j
    rw [σ.symm_apply_apply]
    simp [Pi.single_apply]
  · have he : σ.symm j≠i := by
      intro h
      exact hj (((congrArg σ h).symm.trans (σ.apply_symm_apply j)).symm)
    simp [Pi.single_apply,hj,Ne.symm hj,he,Ne.symm he]

theorem linear_eq_permutation_of_simple_images (e : (I→ℤ)≃ₗ[ℤ](I→ℤ))
    (σ : Equiv.Perm I) (hσ : ∀i,e (Pi.single i 1)=Pi.single (σ i) 1) :
    e=permutationLinear σ := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℤ I).ext
  intro i
  simp only [Pi.basisFun_apply]
  change e (Pi.single i 1)=permutationLinear σ (Pi.single i 1)
  rw [permutationLinear_single]
  exact hσ i

def diagramLinearHom (A : Matrix I I ℤ) :
    diagramGroup A→*((I→ℤ)≃ₗ[ℤ](I→ℤ)) :=
  permutationLinear.comp (diagramGroup A).subtype

def diagramLinearGroup (A : Matrix I I ℤ) :
    Subgroup ((I→ℤ)≃ₗ[ℤ](I→ℤ)) := (diagramLinearHom A).range

theorem diagramLinearGroup_soluble (A : Matrix I I ℤ) [IsSolvable (diagramGroup A)] :
    IsSolvable (diagramLinearGroup A) := by
  exact solvable_of_surjective (f:=(diagramLinearHom A).rangeRestrict)
    (diagramLinearHom A).rangeRestrict_surjective

theorem mem_diagramLinearGroup_of_simple_images (A : Matrix I I ℤ)
    (e : (I→ℤ)≃ₗ[ℤ](I→ℤ)) (σ : Equiv.Perm I)
    (hσ : ∀i,e (Pi.single i 1)=Pi.single (σ i) 1)
    (hA : ∀i j,A (σ i) (σ j)=A i j) : e∈diagramLinearGroup A := by
  refine ⟨⟨σ,hA⟩,?_⟩
  exact (linear_eq_permutation_of_simple_images e σ hσ).symm

end SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction
