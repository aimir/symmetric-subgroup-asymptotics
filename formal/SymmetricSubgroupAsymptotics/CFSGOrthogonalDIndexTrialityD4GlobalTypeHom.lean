import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GlobalTypeCoherence

/-! The globally coherent type permutation is a genuine homomorphism
from the ACTUAL original projective D4 automorphism group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4RootedCliques
variable (K : Type) [Field K] [Finite K]

def typeWitnessNeighbor : Neighbors K :=
  Classical.choose (neighborCoordinate_surjective K (originalResidueBase K))

def typeWitnessClique (t : Fin 3) := rootEdgeClique K (typeWitnessNeighbor K) t

theorem typeWitnessClique_type (t : Fin 3) : naturalCliqueType K (typeWitnessClique K t) = t :=
  rootEdgeClique_type K _ t

theorem typeWitnessClique_maximal (t : Fin 3) :
    MaximalClique (originalPlaneAdjacent K) (typeWitnessClique K t) := rootEdgeClique_maximal K _ t

theorem typeWitnessClique_root (t : Fin 3) : originalRootPlane K ∈ typeWitnessClique K t :=
  root_mem_rootEdgeClique K _ t

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem globalTypePermutation_one : globalTypePermutation K p 1 = 1 := by
  apply Equiv.ext
  intro t
  have hh := global_clique_type_formula K p 1 (originalRootPlane K) (typeWitnessClique K t)
    (typeWitnessClique_maximal K t) (typeWitnessClique_root K t)
  rw [automorphismCliqueImage_one, typeWitnessClique_type] at hh
  exact hh.symm

theorem globalTypePermutation_mul (f g : MulAut (elementaryProjective K 4)) :
    globalTypePermutation K p (f * g) = globalTypePermutation K p f * globalTypePermutation K p g := by
  apply Equiv.ext
  intro t
  let T := typeWitnessClique K t
  have hm : MaximalClique (originalPlaneAdjacent K) T := typeWitnessClique_maximal K t
  have hr : originalRootPlane K ∈ T := typeWitnessClique_root K t
  have ht : naturalCliqueType K T = t := typeWitnessClique_type K t
  have hfg := global_clique_type_formula K p (f * g) (originalRootPlane K) T hm hr
  have hg := global_clique_type_formula K p g (originalRootPlane K) T hm hr
  have hf := global_clique_type_formula K p f (singularActionHom K p 0 g (originalRootPlane K))
    (automorphismCliqueImage K p g T) (automorphismCliqueImage_maximal K p g T hm) ⟨originalRootPlane K, hr, rfl⟩
  rw [ht] at hfg hg
  rw [automorphismCliqueImage_mul] at hfg
  change globalTypePermutation K p (f * g) t = globalTypePermutation K p f (globalTypePermutation K p g t)
  exact hfg.symm.trans (hf.trans (congrArg (globalTypePermutation K p f) hg))

def globalTypeHom : MulAut (elementaryProjective K 4) →* Equiv.Perm (Fin 3) where
  toFun := globalTypePermutation K p
  map_one' := globalTypePermutation_one K p
  map_mul' := globalTypePermutation_mul K p

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
