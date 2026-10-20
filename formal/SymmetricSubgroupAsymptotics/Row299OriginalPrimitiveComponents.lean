import SymmetricSubgroupAsymptotics.Row299OriginalBlockFrame
import SymmetricSubgroupAsymptotics.PrimitiveReferencePairWitness
set_option autoImplicit false
set_option maxRecDepth 8192
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row299OriginalBlockFrame
/- Fixed selected original-coordinate witnesses; no group or normal census. -/
def signedGenerator : Fin 6 → Original :=
  ![originalGenerator 0, originalGenerator 1, originalGenerator 2, (originalGenerator 0)⁻¹, (originalGenerator 1)⁻¹, (originalGenerator 2)⁻¹]
def signedTop : Fin 6 → Equiv.Perm (Fin 2) := ![1, 1, swap, 1, 1, swap⁻¹]
private theorem top_signed (j : Fin 6) : blockFrame.top (signedGenerator j) = signedTop j := by
  fin_cases j <;> simp [signedGenerator, signedTop, map_inv, top_generator, tops]
def pairWord (s : Fin 2) (x y : Fin 6) : List (Fin 6) :=
  ((((#[#[#[[], [], [2, 0, 5, 2, 1, 5], [2, 0, 5, 2, 1, 5, 2, 0, 5, 2, 1, 5], [2, 4, 5, 2, 0, 5, 2, 4, 5, 2, 0, 5], [2, 4, 5, 2, 0, 5]], #[[2, 0, 5], [], [2, 1, 5], [2, 1, 5, 2, 0, 5, 2, 1, 5], [2, 0, 5, 2, 4, 5, 2, 0, 5, 2, 4, 5, 2, 0, 5], [2, 0, 5, 2, 4, 5, 2, 0, 5]], #[[2, 0, 5, 2, 1, 5, 2, 0, 5], [2, 1, 5, 2, 0, 5], [], [2, 1, 5, 2, 1, 5], [2, 1, 5, 2, 1, 5, 2, 0, 5, 2, 1, 5], [2, 4, 5, 2, 0, 5, 2, 1, 5, 2, 0, 5, 2, 1, 5, 2, 0, 5]], #[[2, 0, 5, 2, 1, 5, 2, 0, 5, 2, 1, 5, 2, 0, 5], [2, 1, 5, 2, 0, 5, 2, 1, 5, 2, 0, 5], [2, 1, 5, 2, 1, 5, 2, 0, 5], [], [2, 1, 5, 2, 1, 5, 2, 1, 5], [2, 4, 5, 2, 4, 5, 2, 0, 5, 2, 4, 5]], #[[2, 4, 5, 2, 0, 5, 2, 4, 5], [2, 0, 5, 2, 4, 5, 2, 0, 5, 2, 4, 5], [2, 1, 5, 2, 1, 5, 2, 0, 5, 2, 1, 5, 2, 0, 5], [2, 1, 5, 2, 1, 5, 2, 1, 5, 2, 0, 5], [], [2, 4, 5, 2, 4, 5]], #[[2, 4, 5], [2, 0, 5, 2, 4, 5], [2, 4, 5, 2, 0, 5, 2, 1, 5, 2, 0, 5, 2, 1, 5], [2, 4, 5, 2, 4, 5, 2, 0, 5, 2, 4, 5, 2, 0, 5], [2, 4, 5, 2, 4, 5, 2, 0, 5], []]], #[#[[], [], [1, 0], [1, 0, 1, 0], [0, 4, 0, 4], [0, 4]], #[[1, 0, 4], [], [1], [1, 1, 0], [1, 1, 0, 1, 0], [0, 1, 0, 4]], #[[1, 0, 1, 0, 4], [1, 1, 0, 4], [], [1, 1], [1, 1, 1, 0], [4, 0, 4, 4, 0]], #[[0, 4, 4, 0], [1, 1, 0, 1, 0, 4], [1, 1, 1, 0, 4], [], [1, 1, 1], [4, 4, 0]], #[[4, 0], [4, 0, 1, 0], [4, 0, 1, 0, 1, 0], [4, 4, 0, 4], [], [4, 4]], #[[4], [0], [0, 1, 0], [0, 1, 0, 1, 0], [4, 0, 4], []]]] : Array (Array (Array (List (Fin 6)))))[s.val]!)[x.val]!)[y.val]!)
private theorem word_top : ∀ (s : Fin 2) (x y : Fin 6),
    ((pairWord s x y).map signedTop).prod = 1 := by decide +kernel
def rawWitness (s : Fin 2) (x y : Fin 6) : Original :=
  ((pairWord s x y).map signedGenerator).prod
private theorem rawWitness_top (s : Fin 2) (x y : Fin 6) :
    blockFrame.top (rawWitness s x y) = 1 := by
  simpa only [rawWitness, map_list_prod, List.map_map, Function.comp_def, top_signed] using word_top s x y
def kernelWitness (s : Fin 2) (x y : Fin 6) : blockFrame.top.ker :=
  ⟨rawWitness s x y, rawWitness_top s x y⟩
private theorem pair_points : ∀ (s : Fin 2) (x y : Fin 6), x ≠ y →
    blockFrame.kernelCoordinate s (kernelWitness s x y) 0 = x ∧
    blockFrame.kernelCoordinate s (kernelWitness s x y) 1 = y := by decide +kernel
abbrev Component (s : Fin 2) := (blockFrame.kernelCoordinate s).range
theorem component_two_pretransitive (s : Fin 2) :
    MulAction.IsMultiplyPretransitive (Component s) (Fin 6) 2 := by
  apply two_pretransitive_of_reference_pair (0 : Fin 6) 1
  intro x y hxy
  exact ⟨(blockFrame.kernelCoordinate s).rangeRestrict (kernelWitness s x y), pair_points s x y hxy⟩
instance component_primitive (s : Fin 2) : MulAction.IsPreprimitive (Component s) (Fin 6) :=
  MulAction.isPreprimitive_of_is_two_pretransitive (component_two_pretransitive s)
end SymmetricSubgroupAsymptotics.Row299OriginalBlockFrame
