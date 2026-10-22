import SymmetricSubgroupAsymptotics.CFSGE6GenerationBranchLattice
import SymmetricSubgroupAsymptotics.CFSGE6GenerationTorusPilot
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGeneratedSimpleLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance

/-! The far mixed rational root coefficient belongs to the ORIGINAL
negative fifth generator line because it lies in the SAME generated Lie
algebra, not merely because of its surrounding matrix support. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationFarMixedSimpleLine
open CFSGE6GenerationBranchLattice CFSGE6GenerationLatticePilot
open CFSGE6GenerationTorusPilot CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWordLatticeSupport
open CFSGNormTwoGeckLatticeDegree CFSGGradedMatrixSupport CFSGSerreQuadraticMatrix
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem far_mixed_word_degree :
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      farMixedWord (Pi.single 3 1)= -(Pi.single 5 1 : Fin 6→ℤ) := by
  simp only [farMixedWord,farBranchWord,wordLinear_append,wordLinear_inverseWord,
    LinearEquiv.mul_apply,reflection_two_three]
  change coxeterLinear.symm (coxeterLinear.symm
    ((Pi.single 3 1 : Fin 6→ℤ)+Pi.single 2 1))= -(Pi.single 5 1 : Fin 6→ℤ)
  rw [map_add,map_add,inverse_simple_three,inverse_simple_two,inverse_branch,inverse_simple_zero]
  decide

def farCoefficient (K : Type) [Field K] : Matrix Index Index K :=
  (wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord : Matrix Index Index K)*
    fieldRoot e6Data K false 3*
    (((wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K farMixedWord)⁻¹ :
      Ambient K) : Matrix Index Index K)

theorem rational_far_generated : farCoefficient ℚ∈RootPairing.GeckConstruction.lieAlgebra E6Base :=
  CFSGNormTwoGeckGeneratedLieInvariance.word_action_mem_generated CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index farMixedWord _
    (CFSGNormTwoGeckGeneratedLieInvariance.root_mem_generated CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index false 3)

theorem rational_far_degree :
    Supported (latticeWeight CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base)
      (fun v=>v-(E6Index 5:Roots CartanMatrix.E₆).val) (farCoefficient ℚ) := by
  let e := wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index farMixedWord
  have hP := word_lattice_support CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index ℚ farMixedWord
  have hQ := word_lattice_support CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index ℚ (inverseWord farMixedWord)
  rw [wordUnit_inverseWord,wordLinear_inverseWord] at hQ
  have hE := field_E_lattice_support CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index ℚ 3
  have hh := supported_conjugation
    (latticeWeight CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base)
    e.toAddEquiv (E6Index 3:Roots CartanMatrix.E₆).val _ _ _ hP hE hQ
  change Supported
    (latticeWeight CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base)
    (fun v=>v+wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index
      farMixedWord (Pi.single 3 1)) (farCoefficient ℚ) at hh
  rw [far_mixed_word_degree] at hh
  simpa only [sub_eq_add_neg] using hh

theorem rational_far_simple_line : ∃c : ℚ,
    farCoefficient ℚ=c • RootPairing.GeckConstruction.f (E6Index 5) :=
  CFSGNormTwoCoordinateGeneratedSimpleLine.negative_simple_line CartanMatrix.E₆
    CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos (E6Index 5) (farCoefficient ℚ)
    rational_far_generated rational_far_degree

end SymmetricSubgroupAsymptotics.CFSGE6GenerationFarMixedSimpleLine
