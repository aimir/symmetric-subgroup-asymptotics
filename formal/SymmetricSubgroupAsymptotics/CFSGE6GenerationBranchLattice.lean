import SymmetricSubgroupAsymptotics.CFSGE6GenerationLatticePilot

/-! Selected six-coordinate characters for the two actual branch
conjugate words. These compute scaling exponents only; they do not
identify matrix root operators from their lattice degrees. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchLattice
open CFSGE6GenerationLatticePilot CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordAlgebra

local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def branchVector : Fin 6→ℤ := ![0,1,1,1,1,1]
def farBranchVector : Fin 6→ℤ := ![1,0,1,1,1,0]
def farBranchWord : List (Fin 6) := inverseWord coxeterWord++inverseWord coxeterWord
def farMixedWord : List (Fin 6) := farBranchWord++[2]

theorem coxeter_preimage_three : coxeterMatrix*ᵥbranchVector=Pi.single 3 1 := by decide
theorem coxeter_preimage_branch : coxeterMatrix*ᵥfarBranchVector=branchVector := by decide
theorem coxeter_image_zero : coxeterMatrix*ᵥ(Pi.single 0 1 : Fin 6→ℤ)=Pi.single 2 1 := by decide

theorem inverse_simple_three : coxeterLinear.symm (Pi.single 3 1)=branchVector := by
  have he := LinearMap.congr_fun coxeter_linear_matrix branchVector
  change coxeterMatrix*ᵥbranchVector=coxeterLinear branchVector at he
  rw [coxeter_preimage_three] at he
  exact (congrArg coxeterLinear.symm he).trans (coxeterLinear.symm_apply_apply branchVector)

theorem inverse_branch : coxeterLinear.symm branchVector=farBranchVector := by
  have he := LinearMap.congr_fun coxeter_linear_matrix farBranchVector
  change coxeterMatrix*ᵥfarBranchVector=coxeterLinear farBranchVector at he
  rw [coxeter_preimage_branch] at he
  exact (congrArg coxeterLinear.symm he).trans (coxeterLinear.symm_apply_apply farBranchVector)

theorem inverse_simple_two : coxeterLinear.symm (Pi.single 2 1)=Pi.single 0 1 := by
  have he := LinearMap.congr_fun coxeter_linear_matrix (Pi.single 0 (1:ℤ))
  change coxeterMatrix*ᵥ(Pi.single 0 1 : Fin 6→ℤ)=coxeterLinear (Pi.single 0 1) at he
  rw [coxeter_image_zero] at he
  exact (congrArg coxeterLinear.symm he).trans (coxeterLinear.symm_apply_apply (Pi.single 0 1))

theorem functional_far_branch : torusFunctional farBranchVector=0 := by decide

theorem reflection_two_three :
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index [2] (Pi.single 3 1)=
      (Pi.single 3 1 : Fin 6→ℤ)+Pi.single 2 1 := by
  have he := LinearMap.congr_fun
    (CFSGNormTwoCoordinateLatticeWord.latticeWord_linear CartanMatrix.E₆
      CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
      CartanMatrix.E₆_off_diag_nonpos [2]) (Pi.single 3 (1:ℤ))
  change CFSGSignedCartanReflections.latticeWord CartanMatrix.E₆ [2]*ᵥ
    (Pi.single 3 1 : Fin 6→ℤ)=
      wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index [2] (Pi.single 3 1) at he
  rw [←he]
  decide

theorem far_branch_character : torusFunctional
    (wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index farBranchWord (Pi.single 3 1))=0 := by
  simp only [farBranchWord,wordLinear_append,wordLinear_inverseWord,LinearEquiv.mul_apply]
  change torusFunctional (coxeterLinear.symm (coxeterLinear.symm (Pi.single 3 1)))=0
  rw [inverse_simple_three,inverse_branch,functional_far_branch]

theorem far_mixed_character : torusFunctional
    (wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index farMixedWord (Pi.single 3 1))= -1 := by
  simp only [farMixedWord,farBranchWord,wordLinear_append,wordLinear_inverseWord,
    LinearEquiv.mul_apply,reflection_two_three]
  change torusFunctional (coxeterLinear.symm (coxeterLinear.symm
    ((Pi.single 3 1 : Fin 6→ℤ)+Pi.single 2 1)))= -1
  rw [map_add,map_add,inverse_simple_three,inverse_simple_two,inverse_branch,
    inverse_simple_zero,map_add,functional_far_branch,functional_inverseZero,zero_add]

end SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchLattice
