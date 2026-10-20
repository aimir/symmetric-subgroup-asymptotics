import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets
import SymmetricSubgroupAsymptotics.PrimitiveBoundedCataloguePublishedLocator

/-! The existing116-row actual simple-socle correspondence already supplies
the strict ternary-head consumer on its entire domain. No253-row match is
constructed or assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- A specified perfect normal subgroup contained in every nontrivial
normal subgroup leaves only the actual quotient's prime-order budget. -/
theorem primeRelativeHead_le_quotientFactorization_of_perfect_unique
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] [Group.IsPerfect E]
    (hcontains : ∀ N : Subgroup G,N.Normal → N≠⊥ → E≤N)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N)≤(Nat.card (G⧸E)).factorization p := by
  by_cases hn : N=⊥
  · subst N
    rw [primeRelativeHead_perfect p]
    exact Nat.zero_le _
  · rw [primeRelativeHead_chain_perfect_kernel p E N (hcontains N inferInstance hn)]
    exact primeRelativeHead_le_groupFactorization p (normalChainQuotient E N)

private theorem fiveToEleven_head_receipt :
    ∀ r∈primitiveBoundedIndexRows5To11.toList,
      20*r.outerOrder.factorization 3<3*r.degree ∧
      (r.degree=18 → r.outerOrder.factorization 3=0) := by decide +kernel
private theorem twelveToEighteen_head_receipt :
    ∀ r∈primitiveBoundedIndexRows12To18.toList,
      20*r.outerOrder.factorization 3<3*r.degree ∧
      (r.degree=18 → r.outerOrder.factorization 3=0) := by decide +kernel
private theorem nineteenToTwentyFour_head_receipt :
    ∀ r∈primitiveBoundedIndexRows19To24.toList,
      20*r.outerOrder.factorization 3<3*r.degree ∧
      (r.degree=18 → r.outerOrder.factorization 3=0) := by decide +kernel
private theorem twentyFiveToTwentyNine_head_receipt :
    ∀ r∈primitiveBoundedIndexRows25To29.toList,
      20*r.outerOrder.factorization 3<3*r.degree ∧
      (r.degree=18 → r.outerOrder.factorization 3=0) := by decide +kernel

theorem primitiveBoundedIndexRow_ternaryHead_receipt (i : Fin 116) :
    20*(primitiveBoundedIndexRow i).outerOrder.factorization 3<
      3*(primitiveBoundedIndexRow i).degree ∧
    ((primitiveBoundedIndexRow i).degree=18 →
      (primitiveBoundedIndexRow i).outerOrder.factorization 3=0) := by
  have hm : primitiveBoundedIndexRow i∈primitiveBoundedIndexRows.toList := by
    unfold primitiveBoundedIndexRow
    exact Array.getElem_mem_toList _
  have hc :
      primitiveBoundedIndexRow i∈primitiveBoundedIndexRows5To11.toList ∨
      primitiveBoundedIndexRow i∈primitiveBoundedIndexRows12To18.toList ∨
      primitiveBoundedIndexRow i∈primitiveBoundedIndexRows19To24.toList ∨
      primitiveBoundedIndexRow i∈primitiveBoundedIndexRows25To29.toList := by
    simpa only [primitiveBoundedIndexRows,Array.toList_append,List.mem_append,or_assoc] using hm
  rcases hc with h|h|h|h
  · exact fiveToEleven_head_receipt _ h
  · exact twelveToEighteen_head_receipt _ h
  · exact nineteenToTwentyFour_head_receipt _ h
  · exact twentyFiveToTwentyNine_head_receipt _ h

namespace PublishedBoundedPrimitiveCatalogueLocator
variable {G X : Type} [Group G] [Finite G] [Finite X]
    {E : Subgroup G} [E.Normal] [Group.IsPerfect E]
    (M : PublishedBoundedPrimitiveCatalogueLocator G X E)
    (hcontains : ∀ N : Subgroup G,N.Normal → N≠⊥ → E≤N)

include M hcontains in
theorem ternaryHead_strict (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  have hh := primeRelativeHead_le_quotientFactorization_of_perfect_unique 3 E hcontains N
  calc
    _ ≤ 20*(Nat.card (G⧸E)).factorization 3 := Nat.mul_le_mul_left 20 hh
    _ = 20*(primitiveBoundedIndexRow M.row).outerOrder.factorization 3 := by rw [M.quotientOrder_eq]
    _ < 3*(primitiveBoundedIndexRow M.row).degree :=
      (primitiveBoundedIndexRow_ternaryHead_receipt M.row).1
    _ = 3*Nat.card X := by rw [M.degree_eq]

include M hcontains in
theorem ternaryHead_degreeEighteen_eq_zero (hX : Nat.card X=18)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)=0 := by
  have hh := primeRelativeHead_le_quotientFactorization_of_perfect_unique 3 E hcontains N
  have hd : (primitiveBoundedIndexRow M.row).degree=18 := M.degree_eq.trans hX
  rw [M.quotientOrder_eq,(primitiveBoundedIndexRow_ternaryHead_receipt M.row).2 hd] at hh
  omega

end PublishedBoundedPrimitiveCatalogueLocator
end SymmetricSubgroupAsymptotics
