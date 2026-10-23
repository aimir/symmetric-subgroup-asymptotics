import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSectionDiagramLabels
import SymmetricSubgroupAsymptotics.CFSGCartanDiagramLinearAction

/-! Every positive E6 root has an INTEGRAL diagram-fixed Cartan test
with pairing exactly one. Six tiny simple-seed tests are transported by
actual relative Weyl words. No root census or characteristic restriction
is used, so the resulting folded weights cannot all vanish modulo p. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PrimitiveWeights
open CFSGTwistedE6GeckOriginalRootSections CFSGTwistedE6GeckSectionDiagramLabels
open CFSGTwistedE6WeylChamber CFSGTwistedE6FixedWordClassification
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGCartanDiagramLinearAction
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoCartanDiagramWords CFSGSerreDiagram

private theorem relative_linear_commutes (r : List (Fin 4)) (x : Fin 6 → ℤ) :
    permutationLinear e6Permutation (linearAction (expandRelative r) x) =
      linearAction (expandRelative r) (permutationLinear e6Permutation x) := by
  have he : (permutationLinear e6Permutation).toLinearMap.comp
      (linearAction (expandRelative r)).toLinearMap =
      (linearAction (expandRelative r)).toLinearMap.comp
        (permutationLinear e6Permutation).toLinearMap := by
    apply (Pi.basisFun ℤ (Fin 6)).ext
    intro i
    simp only [LinearMap.comp_apply,Pi.basisFun_apply]
    change permutationLinear e6Permutation
        (linearAction (expandRelative r) (E6Index i : Roots CartanMatrix.E₆).val) =
      linearAction (expandRelative r)
        (permutationLinear e6Permutation (E6Index i : Roots CartanMatrix.E₆).val)
    rw [wordLinear_root]
    change (diagramRoot (rootAction (expandRelative r) (E6Index i))).val =
      linearAction (expandRelative r) (diagramRoot (E6Index i)).val
    rw [wordLinear_root]
    exact congrArg Subtype.val (relative_root_action_commutes r (E6Index i))
  exact LinearMap.congr_fun he x

private theorem wordLinear_pairing (w : List (Fin 6)) (x y : Fin 6 → ℤ) :
    integerPairing CartanMatrix.E₆ (linearAction w x) (linearAction w y) =
      integerPairing CartanMatrix.E₆ x y := by
  have he : (integerPairing CartanMatrix.E₆).compl₁₂
      (linearAction w).toLinearMap (linearAction w).toLinearMap =
      integerPairing CartanMatrix.E₆ := by
    apply (Pi.basisFun ℤ (Fin 6)).ext
    intro i
    apply (Pi.basisFun ℤ (Fin 6)).ext
    intro j
    simp only [LinearMap.compl₁₂_apply,Pi.basisFun_apply]
    change integerPairing CartanMatrix.E₆
        (linearAction w (E6Index i : Roots CartanMatrix.E₆).val)
        (linearAction w (E6Index j : Roots CartanMatrix.E₆).val) =
      integerPairing CartanMatrix.E₆ (E6Index i : Roots CartanMatrix.E₆).val
        (E6Index j : Roots CartanMatrix.E₆).val
    rw [wordLinear_root,wordLinear_root]
    exact wordRoot_integer_pairing CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index w (E6Index i) (E6Index j)
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

def seedTest (j : Fin 6) : Fin 6 → ℤ :=
  ![(Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ), (Pi.single (3 : Fin 6) (1 : ℤ) : Fin 6 → ℤ),
    (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ), (Pi.single (1 : Fin 6) (1 : ℤ) : Fin 6 → ℤ),
    (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ), (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)] j

theorem seedTest_fixed (j : Fin 6) :
    permutationLinear e6Permutation (seedTest j)=seedTest j := by
  fin_cases j
  · change permutationLinear e6Permutation ((Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)) =
      (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    rw [map_add,permutationLinear_single,permutationLinear_single]
    change (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) = (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    exact add_comm _ _
  · change permutationLinear e6Permutation ((Pi.single (3 : Fin 6) (1 : ℤ) : Fin 6 → ℤ))=(Pi.single (3 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    rw [permutationLinear_single]
    rfl
  · change permutationLinear e6Permutation ((Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)) =
      (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    rw [map_add,permutationLinear_single,permutationLinear_single]
    change (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) = (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    exact add_comm _ _
  · change permutationLinear e6Permutation ((Pi.single (1 : Fin 6) (1 : ℤ) : Fin 6 → ℤ))=(Pi.single (1 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    rw [permutationLinear_single]
    rfl
  · change permutationLinear e6Permutation ((Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)) =
      (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    rw [map_add,permutationLinear_single,permutationLinear_single]
    change (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) = (Pi.single (0 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (5 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    exact add_comm _ _
  · change permutationLinear e6Permutation ((Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)) =
      (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    rw [map_add,permutationLinear_single,permutationLinear_single]
    change (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) = (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) + (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ)
    exact add_comm _ _

theorem seedTest_pairing (j : Fin 6) :
    integerPairing CartanMatrix.E₆ (-(E6Index j : Roots CartanMatrix.E₆).val)
      (seedTest j)=1 := by
  change integerPairing CartanMatrix.E₆ (-(Pi.single j (1 : ℤ) : Fin 6 → ℤ)) (seedTest j)=1
  fin_cases j <;> decide

def primitiveTest (k : PositiveRoot) : Fin 6 → ℤ :=
  (linearAction (expandRelative (sectionRelative k))).symm (seedTest (sectionNode k))

theorem primitiveTest_fixed (k : PositiveRoot) :
    permutationLinear e6Permutation (primitiveTest k)=primitiveTest k := by
  apply (linearAction (expandRelative (sectionRelative k))).injective
  rw [←relative_linear_commutes]
  change permutationLinear e6Permutation
      (linearAction (expandRelative (sectionRelative k))
        ((linearAction (expandRelative (sectionRelative k))).symm (seedTest (sectionNode k)))) =
    linearAction (expandRelative (sectionRelative k))
      ((linearAction (expandRelative (sectionRelative k))).symm (seedTest (sectionNode k)))
  rw [LinearEquiv.apply_symm_apply,seedTest_fixed]

theorem primitiveTest_pairing (k : PositiveRoot) :
    integerPairing CartanMatrix.E₆ k.val.val (primitiveTest k)=1 := by
  have he := wordLinear_pairing (expandRelative (sectionRelative k)) k.val.val (primitiveTest k)
  rw [wordLinear_root] at he
  change integerPairing CartanMatrix.E₆
      (rootAction (expandRelative (sectionRelative k)) k.val).val
      (linearAction (expandRelative (sectionRelative k)) (primitiveTest k)) =
    integerPairing CartanMatrix.E₆ k.val.val (primitiveTest k) at he
  rw [section_simple_image] at he
  change integerPairing CartanMatrix.E₆
      (CFSGNormTwoGeckColumns.negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite (E6Index (sectionNode k))).val
      (linearAction (expandRelative (sectionRelative k))
        ((linearAction (expandRelative (sectionRelative k))).symm (seedTest (sectionNode k)))) =
    integerPairing CartanMatrix.E₆ k.val.val (primitiveTest k) at he
  rw [LinearEquiv.apply_symm_apply,CFSGNormTwoGeckColumns.negative_val] at he
  exact he.symm.trans (seedTest_pairing (sectionNode k))

theorem exists_fixed_primitive_test (k : PositiveRoot) :
    ∃h : Fin 6 → ℤ, permutationLinear e6Permutation h=h ∧
      integerPairing CartanMatrix.E₆ k.val.val h=1 :=
  ⟨primitiveTest k,primitiveTest_fixed k,primitiveTest_pairing k⟩

end SymmetricSubgroupAsymptotics.CFSGFFourE6PrimitiveWeights
