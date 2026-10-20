import SymmetricSubgroupAsymptotics.BinaryExcessNormalFiltration
import SymmetricSubgroupAsymptotics.BinaryProductNormalHalfDegree

/-! The exact ordinary maximal-tail estimate from local proper-normal
bounds on original dependent factors. This is a general implication and
declares no new published input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryExcessWeightedTail

open MarkedC4 MarkedC4.RDTOriginalWordStructure
open BinaryExcessMaximalTailAxes

private theorem sum_subtype_eq_indicator {A : Type} [Fintype A]
    (p : A → Prop) (f : A → ℝ) :
    (∑ a : {a // p a}, f a.val) = ∑ a : A, if p a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter p) (by simp) f).symm

/-- The full tail is charged its unconditional binary half-degree bound;
only proper normal subgroups enter the dependent-factor hypothesis. -/
theorem normalGen_le
    {t : ℕ} (n : Fin t → ℕ)
    (K : ∀ i, Subgroup (Equiv.Perm (Fin (n i))))
    (hK : ∀ i, IsPGroup 2 (K i))
    (L : Subgroup (∀ i, K i))
    (hfull : ∀ i, Function.Surjective (coordinate (fun i => K i) L i))
    (tail : Finset (Fin t)) (hmax : MaximalTail (fun i => K i) L tail)
    (N : Subgroup L) [N.Normal] (c : ℝ)
    (hlocal : ∀ i, i ∉ tail → ∀ V : Subgroup (K i), V.Normal → V ≠ ⊤ →
      (normalGen V : ℝ) ≤ c * n i) :
    (normalGen N : ℝ) ≤ c * dependentDegree n tail + tailDegree n tail / 2 := by
  letI : Fintype {j : Fin t // j ∈ tail} := Subtype.fintype (fun j => j ∈ tail)
  let f := tailProjection (fun i => K i) L tail
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hmax.1
  have ht := BinaryProductNormalHalfDegree.normalGen_le
    (fun i : {j // j ∈ tail} => n i.val)
    (fun i : {j // j ∈ tail} => K i.val)
    (fun i => hK i.val) (N.map f)
  have hsum : (∑ i : {j // j ∈ tail}, (n i.val : ℝ)) = tailDegree n tail := by
    unfold tailDegree
    convert sum_subtype_eq_indicator (fun i => i ∈ tail) (fun i => (n i : ℝ)) using 1
    apply Finset.sum_congr
    · ext i; simp
    · intro i _; rfl
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ tail <;> simp [hi]
  rw [hsum] at ht
  have hd : (∑ i : Fin t, if i ∈ tail then 0 else c * (n i : ℝ)) =
      c * dependentDegree n tail := by
    unfold dependentDegree
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have hh := BinaryExcessNormalFiltration.normalGen_le_kernel_weights_add_tail
    (fun i => K i) L hfull tail hmax N (fun i => c * (n i : ℝ)) hlocal
  rw [hd] at hh
  exact hh.trans (add_le_add le_rfl ht)

end SymmetricSubgroupAsymptotics.BinaryExcessWeightedTail
