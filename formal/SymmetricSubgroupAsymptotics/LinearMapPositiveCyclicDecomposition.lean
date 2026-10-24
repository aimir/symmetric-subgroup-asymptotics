import SymmetricSubgroupAsymptotics.LinearMapMonicCyclicDecomposition

/-! Zero cyclic summands can be discarded from the actual polynomial
module decomposition. The remaining monic polynomial degrees are
positive, sum to the dimension, and bound the number of summands. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
namespace SymmetricSubgroupAsymptotics.LinearMapPositiveCyclicDecomposition
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

structure Chart (A : Module.End K V) where
  ι : Type u
  [fintype : Fintype ι]
  polynomial : ι → K[X]
  monic : ∀ i, (polynomial i).Monic
  positive : ∀ i, 0 < (polynomial i).natDegree
  equiv : Module.AEval' A ≃ₗ[K[X]]
    (i : ι) → K[X] ⧸ Submodule.span K[X] ({polynomial i} : Set K[X])

attribute [instance] Chart.fintype

private def restrictPositive {A : Module.End K V}
    (C : LinearMapMonicCyclicDecomposition.Chart A) :
    ((i : C.ι) → K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X])) ≃ₗ[K[X]]
      ((i : {i : C.ι // 0 < (C.polynomial i).natDegree}) →
        K[X] ⧸ Submodule.span K[X] ({C.polynomial i.val} : Set K[X])) := by
  classical
  refine {
    toFun := fun v i => v i.val
    invFun := fun v i => if h : 0 < (C.polynomial i).natDegree then v ⟨i, h⟩ else 0
    left_inv := ?_
    right_inv := ?_
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  · intro z
    funext i
    by_cases h : 0 < (C.polynomial i).natDegree
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      have hp : C.polynomial i = 1 := eq_one_of_monic_natDegree_zero (C.monic i) (by omega)
      have ht : Submodule.span K[X] ({C.polynomial i} : Set K[X]) = ⊤ := by simp [hp]
      letI : Subsingleton (K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X])) :=
        Submodule.Quotient.subsingleton_iff.mpr ht
      exact Subsingleton.elim _ _
  · intro z
    funext i
    simp only [dif_pos i.property]

set_option backward.isDefEq.respectTransparency false in
theorem exists_chart (A : Module.End K V) : Nonempty (Chart A) := by
  classical
  let C := LinearMapMonicCyclicDecomposition.chart A
  exact ⟨⟨{i : C.ι // 0 < (C.polynomial i).natDegree},
    fun i => C.polynomial i.val, fun i => C.monic i.val, fun i => i.property,
    C.equiv.trans (DFinsupp.linearEquivFunOnFintype.trans (restrictPositive C))⟩⟩

def chart (A : Module.End K V) : Chart A := Classical.choice (exists_chart A)

theorem Chart.degree_sum {A : Module.End K V} (C : Chart A) :
    (∑ i : C.ι, (C.polynomial i).natDegree) = Module.finrank K V := by
  letI (i : C.ι) : Module.Finite K
      (K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X])) := (C.monic i).finite_quotient
  calc
    _ = Module.finrank K ((i : C.ι) →
        K[X] ⧸ Submodule.span K[X] ({C.polynomial i} : Set K[X])) := by
      rw [Module.finrank_pi_fintype]
      simp_rw [finrank_quotient_span_eq_natDegree]
    _ = Module.finrank K (Module.AEval' A) := (C.equiv.restrictScalars K).finrank_eq.symm
    _ = Module.finrank K V := (Module.AEval'.of A).finrank_eq.symm

theorem Chart.card_le_dimension {A : Module.End K V} (C : Chart A) :
    Nat.card C.ι ≤ Module.finrank K V := by
  calc
    Nat.card C.ι = ∑ _i : C.ι, 1 := by simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ i : C.ι, (C.polynomial i).natDegree := Finset.sum_le_sum (fun i _ => C.positive i)
    _ = Module.finrank K V := C.degree_sum

end SymmetricSubgroupAsymptotics.LinearMapPositiveCyclicDecomposition
