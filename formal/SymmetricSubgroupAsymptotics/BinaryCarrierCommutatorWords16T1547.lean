import SymmetricSubgroupAsymptotics.BinaryCarrierDerivedCharacters16T1547
import SymmetricSubgroupAsymptotics.PrimeDerivedCommutatorPairing

/-! Exact original-generator commutator coefficients. Every group equation
is checked on the sixteen original points. The coefficients apply to all
whole-original-group invariant derived characters through their actual
three-coordinate equivalence. The derived subgroup need not be abelian;
all invariant characters retain conjugation by the whole original group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1547

open BinaryCarrierDerivedCharacters16T1547

private abbrev g := BinaryActionData16.node1547Generators
private abbrev words := BinaryCarrierDerivedOrder16T1547.basisWords

private def commutatorWords (i j : Fin 6) : List (Fin 5) :=
  ![![[], [], [], [0], [1], [2]],
    ![[], [], [1,1,2], [3], [4], [0,1,2,4,3]],
    ![[], [1,1,2], [], [0,1,1,4], [1,4,3], [0,1,1,4]],
    ![[0], [0,3,0], [0,1,1,4], [], [0,4], []],
    ![[0,1,0], [4], [1,4,3], [0,4], [], [1,0]],
    ![[2], [0,1,2,4,3], [0,1,1,4], [], [1,0], []]] i j

/-- Three-coordinate scalar coefficients, in original generator order. -/
def values (v : Fin 3 → ZMod 2) (i j : Fin 6) : ZMod 2 :=
  ![![0, 0, 0, v 0, v 1, v 2],
    ![0, 0, v 2, v 1, v 0, v 2],
    ![0, v 2, 0, 0, v 0, 0],
    ![v 0, v 1, 0, 0, 0, 0],
    ![v 1, v 0, v 0, 0, 0, v 0+v 1],
    ![v 2, v 2, 0, 0, v 0+v 1, 0]] i j

private theorem original_pointwise : ∀ (i j : Fin 6) (x : Fin 16),
    (((commutatorWords i j).map (fun k => (words k).eval g)).prod) x =
      ⁅g i,g j⁆ x := by decide +kernel

theorem original_commutator_word (i j : Fin 6) :
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

private theorem character_word (χ : Characters) (w : List (Fin 5)) :
    χ.1 (Additive.ofMul ((w.map originalBasis).prod)) =
      (w.map (fun k => χ.1 (Additive.ofMul (originalBasis k)))).sum := by
  induction w with
  | nil => exact χ.1.map_zero
  | cons k w ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    change χ.1 (Additive.ofMul (originalBasis k) + Additive.ofMul ((w.map originalBasis).prod)) =
      χ.1 (Additive.ofMul (originalBasis k)) + _
    rw [map_add, ih]

/-- Scalar reduction of the literal word under the actual character chart. -/
private theorem word_values : ∀ (v : Fin 3 → ZMod 2) (i j : Fin 6),
    ((commutatorWords i j).map
      (fun k => ((quotientWords k).map v).sum)).sum = values v i j := by
  decide +kernel

/-- The actual character pairing equals the displayed scalar matrix;
no catalogue or independently chosen matrix is substituted. -/
theorem original_commutator_value (χ : Characters) (i j : Fin 6) :
    derivedCharacterCommutator 2 χ (closureGenerators g i) (closureGenerators g j) =
      values (coordinates χ) i j := by
  change χ.1 (Additive.ofMul (derivedCommutatorElement
    (closureGenerators g i) (closureGenerators g j))) = _
  rw [← original_commutator_word, character_word]
  simp_rw [originalBasis_value]
  exact word_values (coordinates χ) i j

end SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1547
