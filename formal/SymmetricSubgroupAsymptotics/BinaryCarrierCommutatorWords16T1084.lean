import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T1084
import SymmetricSubgroupAsymptotics.PrimeDerivedCommutatorPairing

/-! Full original-generator commutator values for the literal 16T1084
action. The words reuse the checked original derived-row certificate.
All seven original ambient generators are retained. Scalar values follow
from the actual whole-group invariant character chart, not from a
substituted numerical matrix or a reduced ambient generating family. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1084

open BinaryCarrierDerivedCharacters16T1084

private abbrev g := BinaryActionData16.node1084Generators
private abbrev words := BinaryCarrierDerivedOrder16T1084.basisWords
private abbrev C := BinaryCarrierDerivedOrder16T1084.certificate

/-- The full original commutator row, expressed in the checked derived basis. -/
private def commutatorWords (i j : Fin 7) : List (Fin 4) :=
  C.cayley.words (C.commutatorRow i j)

/-- Character values retain the full seven-generator order. The chart
relations remove precisely the actual relative-radical contributions. -/
def values (v : Fin 3 → ZMod 2) (i j : Fin 7) : ZMod 2 :=
  ((commutatorWords i j).map (fun k => ((quotientWords k).map v).sum)).sum

/-- The checked row word is the same original commutator inside D. -/
theorem original_commutator_word (i j : Fin 7) :
    ((commutatorWords i j).map originalBasis).prod =
      derivedCommutatorElement (closureGenerators g i) (closureGenerators g j) := by
  apply Subtype.ext
  change D.subtype (((commutatorWords i j).map originalBasis).prod) =
    ⁅closureGenerators g i, closureGenerators g j⁆
  rw [map_list_prod, List.map_map]
  change ((commutatorWords i j).map (derivedWordGenerators g words)).prod = _
  exact (C.cayley.words_eq (C.commutatorRow i j)).symm.trans (C.commutator_eq i j)

private theorem character_word (χ : Characters) (w : List (Fin 4)) :
    χ.1 (Additive.ofMul ((w.map originalBasis).prod)) =
      (w.map (fun k => χ.1 (Additive.ofMul (originalBasis k)))).sum := by
  induction w with
  | nil => exact χ.1.map_zero
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    change χ.1 (Additive.ofMul (originalBasis k) + Additive.ofMul ((w.map originalBasis).prod)) =
      χ.1 (Additive.ofMul (originalBasis k)) + _
    rw [map_add, ih]

/-- Exact character pairing for every pair of the seven original ambient
generators and every whole-original-group invariant derived character. -/
theorem original_commutator_value (χ : Characters) (i j : Fin 7) :
    derivedCharacterCommutator 2 χ (closureGenerators g i) (closureGenerators g j) =
      values (coordinates χ) i j := by
  change χ.1 (Additive.ofMul (derivedCommutatorElement
    (closureGenerators g i) (closureGenerators g j))) = _
  rw [← original_commutator_word, character_word]
  unfold values
  simp only [originalBasis_value]

end SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1084
