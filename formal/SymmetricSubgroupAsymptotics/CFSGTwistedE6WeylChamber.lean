import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateInversionCount
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordNormalizer
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
import SymmetricSubgroupAsymptotics.CFSGNormTwoCartanDiagramWords
import SymmetricSubgroupAsymptotics.CFSGSerreConcreteDiagrams
import Mathlib.Data.ZMod.Basic

/-! The literal E6 Weyl action has a negative simple image unless it is
the identity. This uses the already proved integral E6 chamber rigidity,
tested in a finite coefficient field, not a Weyl-group census. Diagram
commutation propagates that negative image to its entire node orbit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6WeylChamber
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormalizerWordIdentity CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinatePositiveWordNormalizer CFSGNormTwoCartanDiagramRoots
open CFSGNormTwoCartanDiagramWords CFSGSerreDiagram

abbrev linearAction := wordLinear CartanMatrix.E₆ CartanMatrix.E₆_transpose
  E6_positive_definite E6Base E6Index
abbrev rootAction := wordRoot CartanMatrix.E₆ CartanMatrix.E₆_transpose
  E6_positive_definite E6Base E6Index
abbrev diagramRoot := rootPermutation CartanMatrix.E₆ e6Permutation e6_preserves

theorem positive_simple_identity (w : List (Fin 6))
    (hw : ∀i j,0≤(rootAction w (E6Index i)).val j) : linearAction w=1 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact E6_normalizer_word_identity (ZMod 2) w
    (positive_word_mem_normalizer CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos (ZMod 2) w hw)

theorem exists_negative_simple (w : List (Fin 6)) (hw : linearAction w≠1) :
    ∃i : Fin 6,∀j,(rootAction w (E6Index i)).val j≤0 := by
  by_contra hnone
  apply hw
  apply positive_simple_identity w
  intro i
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign CartanMatrix.E₆
      CartanMatrix.E₆_transpose E6_positive_definite
      (fun j=>by rw [CartanMatrix.E₆_diag j];exact even_two)
      CartanMatrix.E₆_off_diag_nonpos (rootAction w (E6Index i)).val
      (rootAction w (E6Index i)).property with hpos|hneg
  · exact hpos
  · exact False.elim (hnone ⟨i,hneg⟩)

theorem negative_simple_partner (w : List (Fin 6))
    (hcomm : ∀k,diagramRoot (rootAction w k)=rootAction w (diagramRoot k))
    (i : Fin 6) (hi : ∀j,(rootAction w (E6Index i)).val j≤0) :
    ∀j,(rootAction w (E6Index (e6Permutation i))).val j≤0 := by
  have he : diagramRoot (rootAction w (E6Index i))=
      rootAction w (E6Index (e6Permutation i)) := by
    rw [hcomm]
    exact congrArg (rootAction w)
      (simple_rootPermutation CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
        E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation e6_preserves i)
  intro j
  calc
    (rootAction w (E6Index (e6Permutation i))).val j=
        (diagramRoot (rootAction w (E6Index i))).val j :=
      congrArg (fun k : Roots CartanMatrix.E₆=>k.val j) he.symm
    _=(rootAction w (E6Index i)).val (e6Permutation.symm j) := rfl
    _≤0 := hi _

end SymmetricSubgroupAsymptotics.CFSGTwistedE6WeylChamber
