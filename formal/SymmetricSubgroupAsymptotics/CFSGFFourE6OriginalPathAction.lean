import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveCommutationPath
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleRootRanges
import SymmetricSubgroupAsymptotics.CFSGSubgroupCommutationPermutation

/-! An ORIGINAL opposed-Sylow stabilizer acts on the actual simple
charts by a path automorphism. The label image has at most two elements;
reversal is retained in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPathAction
open CFSGFFourE6PositiveCommutationPath CFSGFFourE6OriginalRootAction
open CFSGFFourE6OriginalRootIntersection CFSGFFourE6OriginalSimpleRootRanges
open CFSGFFourE6OriginalProjection CFSGFFourE6OriginalOppositeAlignment
open CFSGSubgroupCommutationPermutation CFSGFourRootPathPermutation CFSG.Models.Chevalley

theorem original_root_graph (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (i j : Fin 4) :
    SubgroupsCommute (originalOrbitRoot K i) (originalOrbitRoot K j) ↔ ¬ adjacent i j := by
  rw [originalOrbitRoot_eq_simple_range, originalOrbitRoot_eq_simple_range, ranges_commute_iff]
  exact original_charts_commute_iff_nonadjacent K p i j

theorem exists_original_path_permutation (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map f.toMonoidHom =
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)))
    (hV : (originalNegative K).map f.toMonoidHom = originalNegative K) :
    ∃ sigma : pathAut, ∀ a : Fin 4,
      (originalOrbitRoot K a).map f.toMonoidHom = originalOrbitRoot K (sigma.val a) := by
  obtain ⟨sigma, hsigma⟩ := exists_original_root_permutation K p f hU hV
  exact ⟨⟨sigma, path_preserved (originalOrbitRoot K) (original_root_graph K p) f sigma hsigma⟩, hsigma⟩

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPathAction
