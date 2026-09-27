import SymmetricSubgroupAsymptotics.TransitiveBinaryNormalHead
import SymmetricSubgroupAsymptotics.PGroupNormalSubgroupCount
import SymmetricSubgroupAsymptotics.BinaryPermutationOrder

/-!
# Counting original normals in a transitive binary action

The proved cumulative Boolean-width head bound is installed for every
normal subgroup of the actual permutation group. A source-order bound
then includes every original normal in the actual index cutoff. Neither
head monotonicity nor an independently supplied head bound is used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {X : Type} [Finite X]

/-- Bounded-index counting inside any original normal M. Normality and
the relative heads are still taken in the entire original U. -/
theorem transitiveBinary_normal_count_atMostIndex_le
    (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) (M : Subgroup U) [M.Normal] (a : ℕ) :
    Nat.card (NormalSubgroupsAtMostIndex M (2^a)) ≤
      2^(a * binaryCumulativeWidth k) := by
  apply pGroup_normal_subgroup_count_le hU M (binaryCumulativeWidth k)
  intro L _ _
  exact transitiveBinary_normal_relativeHead_le_cumulative k U hU hdegree L

/-- Every literal original normal has index at most the actual source
order. The inclusion into the index cutoff preserves the subgroup itself. -/
theorem transitiveBinary_normal_count_le
    (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) (a : ℕ) (horder : Nat.card U ≤ 2^a) :
    Nat.card {N : Subgroup U // N.Normal} ≤
      2^(a * binaryCumulativeWidth k) := by
  let f : {N : Subgroup U // N.Normal} →
      NormalSubgroupsAtMostIndex (⊤ : Subgroup U) (2^a) := fun N =>
    ⟨N.1,N.2,le_top,by
      rw [Subgroup.relIndex_top_right]
      exact (Nat.le_of_dvd (Nat.card_pos (α := U)) N.1.index_dvd_card).trans horder⟩
  have hf : Function.Injective f := by
    intro N N' h
    apply Subtype.ext
    exact congrArg
      (fun L : NormalSubgroupsAtMostIndex (⊤ : Subgroup U) (2^a) => L.1) h
  exact (Nat.card_le_card_of_injective f hf).trans
    (transitiveBinary_normal_count_atMostIndex_le k U hU hdegree ⊤ a)

/-- The same all-normal count on the literal degree-2^k point set. -/
theorem transitiveBinary_literal_normal_count_le
    (k : ℕ) (U : Subgroup (Equiv.Perm (Fin (2^k))))
    [MulAction.IsPretransitive U (Fin (2^k))] (hU : IsPGroup 2 U)
    (a : ℕ) (horder : Nat.card U ≤ 2^a) :
    Nat.card {N : Subgroup U // N.Normal} ≤
      2^(a * binaryCumulativeWidth k) :=
  transitiveBinary_normal_count_le k U hU (Nat.card_fin _) a horder

/-- The original permutation degree supplies the order bound internally. -/
theorem transitiveBinary_normal_count_le_degree
    (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^k) :
    Nat.card {N : Subgroup U // N.Normal} ≤
      2^((2^k-1) * binaryCumulativeWidth k) :=
  transitiveBinary_normal_count_le k U hU hdegree (2^k-1)
    (binary_permutation_card_le k hdegree U hU)

end SymmetricSubgroupAsymptotics

end
