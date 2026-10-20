import SymmetricSubgroupAsymptotics.EvenTwelvePointSubgroupOrder110
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage
import SymmetricSubgroupAsymptotics.PerfectSubdirect
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Exact exclusion of the sole two-action degree12 residual arithmetic
case. A transitive action of order1320 has a stabilizer of order110, while
perfectness makes its literal faithful permutation image even. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

/-- No perfect group of order1320 has a faithful transitive twelve-point
action. This is stronger than the simple-group exclusion needed below. -/
theorem no_perfect_order1320_twelvePoint_action
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPretransitive G X] [Group.IsPerfect G]
    (hG : Nat.card G=1320) (hX : Nat.card X=12) : False := by
  let points : X≃Fin 12 := Finite.equivFinOfCardEq hX
  let f : G→*Equiv.Perm (Fin 12) := labelledActionHom points
  have hf : Function.Injective f := labelledActionHom_injective points
  let K := MulAction.stabilizer G (points.symm 0)
  have hi : K.index=12 := (MulAction.index_stabilizer_of_transitive G (points.symm 0)).trans hX
  have hK : Nat.card K=110 := by
    have hm := K.card_mul_index
    rw [hi,hG] at hm
    omega
  let H := K.map f
  have hH : Nat.card H=110 :=
    (Nat.card_congr (K.equivMapOfInjective f hf).toEquiv).symm.trans hK
  let chi := Equiv.Perm.sign.comp f
  have hchi : ∀ g:G,chi g=1 := by
    intro g
    exact Abelianization.commutator_subset_ker chi (Group.IsPerfect.mem_commutator (g := g))
  apply no_even_twelvePoint_subgroup_order110 H hH
  rintro h ⟨g,hg,rfl⟩
  exact hchi g

/-- In particular the simple factor of the exceptional arithmetic pair
cannot have order1320 and least index12. -/
theorem no_nonabelian_simple_order1320_twelvePoint_action
    {G X : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [Finite X] [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hnc : ¬IsMulCommutative G) (hG : Nat.card G=1320) (hX : Nat.card X=12) : False := by
  letI : Group.IsPerfect G := simple_perfect_of_nonabelian hnc
  exact no_perfect_order1320_twelvePoint_action hG hX

end SymmetricSubgroupAsymptotics
