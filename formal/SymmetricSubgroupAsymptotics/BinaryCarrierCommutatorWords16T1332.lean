import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T1332
import SymmetricSubgroupAsymptotics.PrimeDerivedCommutatorPairing

/-! Literal commutators of the five original 16T1332 generators.
All twenty-five group equations are checked on the original sixteen
points. Their scalar values use the complete whole-group invariant
derived-character chart, even though the derived subgroup is nonabelian.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1332

open BinaryCarrierDerivedCharacters16T1332

private abbrev g := BinaryActionData16.node1332Generators
private abbrev words := BinaryCarrierDerivedOrder16T1332.basisWords

private def commutatorWords (i j : Fin 5) : List (Fin 6) :=
  ![![[], [], [0], [], [1]],
    ![[], [], [2], [2], [3]],
    ![[0], [2], [], [0], [4]],
    ![[], [2], [0], [], [5]],
    ![[1], [3], [0,2,4], [0,2,5], []]] i j

/-- Four-coordinate values in the literal original-generator order. -/
def values (v : Fin 4 → ZMod 2) (i j : Fin 5) : ZMod 2 :=
  ![![0, 0, 0, 0, v 0],
    ![0, 0, 0, 0, v 1],
    ![0, 0, 0, 0, v 2],
    ![0, 0, 0, 0, v 3],
    ![v 0, v 1, v 2, v 3, 0]] i j

private theorem original_pointwise : ∀ (i j : Fin 5) (x : Fin 16),
    (((commutatorWords i j).map (fun k => (words k).eval g)).prod) x =
      ⁅g i,g j⁆ x := by decide +kernel

theorem original_commutator_word (i j : Fin 5) :
    ((commutatorWords i j).map originalBasis).prod =
      derivedCommutatorElement (closureGenerators g i) (closureGenerators g j) := by
  apply Subtype.ext
  apply Subtype.ext
  let projection : D →* Equiv.Perm (Fin 16) := Original.subtype.comp D.subtype
  change projection (((commutatorWords i j).map originalBasis).prod) = ⁅g i,g j⁆
  have hf : projection ∘ originalBasis = fun k => (words k).eval g := by
    funext k
    exact closureGenerators_eval_coe g (words k)
  rw [map_list_prod, List.map_map, hf]
  exact Equiv.ext (original_pointwise i j)

private theorem character_word (χ : Characters) (w : List (Fin 6)) :
    χ.1 (Additive.ofMul ((w.map originalBasis).prod)) =
      (w.map (fun k => χ.1 (Additive.ofMul (originalBasis k)))).sum := by
  induction w with
  | nil => exact χ.1.map_zero
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    change χ.1 (Additive.ofMul (originalBasis k) + Additive.ofMul ((w.map originalBasis).prod)) =
      χ.1 (Additive.ofMul (originalBasis k)) + _
    rw [map_add, ih]

private theorem word_values : ∀ (v : Fin 4 → ZMod 2) (i j : Fin 5),
    ((commutatorWords i j).map
      (fun k => ((quotientWords k).map v).sum)).sum = values v i j := by
  decide +kernel

/-- Every original invariant character has precisely these commutator
values; no extension of the character to Original is assumed. -/
theorem original_commutator_value (χ : Characters) (i j : Fin 5) :
    derivedCharacterCommutator 2 χ (closureGenerators g i) (closureGenerators g j) =
      values (coordinates χ) i j := by
  change χ.1 (Additive.ofMul (derivedCommutatorElement
    (closureGenerators g i) (closureGenerators g j))) = _
  rw [← original_commutator_word, character_word]
  simp_rw [originalBasis_value]
  exact word_values (coordinates χ) i j

end SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1332
