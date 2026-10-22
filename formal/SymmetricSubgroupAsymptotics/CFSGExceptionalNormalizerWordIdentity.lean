import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordDiagramAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGE6WeylDiscriminant
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases

/-! Original E6/E7/E8 positive-normalizing Weyl words have trivial lattice
action. E6 uses the integral mod-three discriminant obstruction, so no
coefficient-field characteristic is excluded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinateWordDiagramAction
open CFSGCartanDiagramLinearAction CFSGExceptionalDiagramAutomorphisms
open CFSGNormTwoCoordinateLatticeWord
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₈) := Classical.decEq _

theorem E6_normalizer_word_identity (K : Type) [Field K] (w : List (Fin 6))
    (hn : wordUnit CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K w∈
      Subgroup.normalizer (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index K false : Set _)) :
    wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index w=1 := by
  obtain ⟨σ,he,hA⟩ := normalizer_word_action CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K w hn
  change wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index w=
    permutationLinear σ at he
  have hσ : σ=1 := CFSGE6WeylDiscriminant.diagram_eq_one_of_word_action w σ hA (by
    intro x
    have hh := LinearMap.congr_fun (latticeWord_linear CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos w) x
    change CFSGSignedCartanReflections.latticeWord CartanMatrix.E₆ w*ᵥx=
      wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index w x at hh
    rw [he] at hh
    exact hh)
  rw [he,hσ,map_one]

theorem E7_normalizer_word_identity (K : Type) [Field K] (w : List (Fin 7))
    (hn : wordUnit CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite E7Base E7Index K w∈
      Subgroup.normalizer (rootGroup CartanMatrix.E₇ CartanMatrix.E₇_transpose
        E7_positive_definite E7Base E7Index K false : Set _)) :
    wordLinear CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite E7Base E7Index w=1 := by
  obtain ⟨σ,he,hA⟩ := normalizer_word_action CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos K w hn
  change wordLinear CartanMatrix.E₇ CartanMatrix.E₇_transpose E7_positive_definite E7Base E7Index w=
    permutationLinear σ at he
  rw [he,E7_rigid σ hA,map_one]

theorem E8_normalizer_word_identity (K : Type) [Field K] (w : List (Fin 8))
    (hn : wordUnit CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite E8Base E8Index K w∈
      Subgroup.normalizer (rootGroup CartanMatrix.E₈ CartanMatrix.E₈_transpose
        E8_positive_definite E8Base E8Index K false : Set _)) :
    wordLinear CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite E8Base E8Index w=1 := by
  obtain ⟨σ,he,hA⟩ := normalizer_word_action CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos K w hn
  change wordLinear CartanMatrix.E₈ CartanMatrix.E₈_transpose E8_positive_definite E8Base E8Index w=
    permutationLinear σ at he
  rw [he,E8_rigid σ hA,map_one]

end SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
