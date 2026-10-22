import SymmetricSubgroupAsymptotics.CFSGSylowProductProjection
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Algebra.Pointwise.Stabilizer

/-! Literal independent coordinate projections of a symmetric Sylow
subgroup preserving a subset. The split embedding is the actual
sum-complement chart; pure projected elements stay in the SAME Sylow. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
open Equiv MulAction
variable {X : Type*} [DecidableEq X] (s : Set X)

def splitEmbedding : Perm s × Perm (sᶜ : Set X) →* Perm X :=
  (Equiv.sumCompl (fun x => x ∈ s)).permCongrHom.toMonoidHom.comp
    (Perm.sumCongrHom s (sᶜ : Set X))

theorem splitEmbedding_apply_mem (a : Perm s) (b : Perm (sᶜ : Set X)) {x : X} (hx : x ∈ s) :
    splitEmbedding s (a, b) x = (a ⟨x, hx⟩).val := by
  change Equiv.sumCompl (fun x => x ∈ s)
    (Equiv.sumCongr a b ((Equiv.sumCompl (fun x => x ∈ s)).symm x)) = _
  rw [Equiv.sumCompl_symm_apply_of_pos hx]
  rfl

theorem splitEmbedding_apply_notMem (a : Perm s) (b : Perm (sᶜ : Set X)) {x : X} (hx : x ∉ s) :
    splitEmbedding s (a, b) x = (b ⟨x, hx⟩).val := by
  change Equiv.sumCompl (fun x => x ∈ s)
    (Equiv.sumCongr a b ((Equiv.sumCompl (fun x => x ∈ s)).symm x)) = _
  rw [Equiv.sumCompl_symm_apply_of_neg hx]
  rfl

theorem splitEmbedding_injective : Function.Injective (splitEmbedding s) :=
  (Equiv.sumCompl (fun x => x ∈ s)).permCongrHom.injective.comp
    Perm.sumCongrHom_injective

theorem mem_range_of_stabilizes {g : Perm X}
    (hg : g ∈ MulAction.stabilizer (Perm X) s) : g ∈ (splitEmbedding s).range := by
  have he : ∀ x : X, g x ∈ s ↔ x ∈ s := MulAction.mem_stabilizer_set.mp hg
  let a : Perm s := g.subtypePerm he
  let b : Perm (sᶜ : Set X) := g.subtypePerm (fun x => (he x).not)
  refine ⟨(a, b), ?_⟩
  apply Perm.ext
  intro x
  by_cases hx : x ∈ s
  · rw [splitEmbedding_apply_mem s a b hx]
    rfl
  · rw [splitEmbedding_apply_notMem s a b hx]
    rfl

variable [Finite X]

def splitSylow (P : Sylow 2 (Perm X))
    (hP : (P : Subgroup (Perm X)) ≤ MulAction.stabilizer (Perm X) s) :
    Sylow 2 (Perm s × Perm (sᶜ : Set X)) :=
  P.comapOfInjective (splitEmbedding s) (splitEmbedding_injective s)
    (fun _ hg => mem_range_of_stabilizes s (hP hg))

theorem pure_projections_mem (P : Sylow 2 (Perm X))
    (hP : (P : Subgroup (Perm X)) ≤ MulAction.stabilizer (Perm X) s)
    (a : Perm s) (b : Perm (sᶜ : Set X)) (hab : splitEmbedding s (a, b) ∈ P) :
    splitEmbedding s (a, 1) ∈ P ∧ splitEmbedding s (1, b) ∈ P := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := splitSylow s P hP
  have hh : (a, b) ∈ Q := hab
  exact ⟨CFSGSylowProductProjection.fst_pure_mem Q hh,
    CFSGSylowProductProjection.snd_pure_mem Q hh⟩

end SymmetricSubgroupAsymptotics.CFSGPermutationSubsetProduct
