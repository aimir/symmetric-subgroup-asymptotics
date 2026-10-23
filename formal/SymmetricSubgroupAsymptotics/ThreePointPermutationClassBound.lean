import SymmetricSubgroupAsymptotics.PrimeIndexAbelianClassCount
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The degree-three component budget, including its nonabelian full
permutation group. The full group is counted by its ACTUAL alternating
kernel of index two; proper subgroups are bounded by Lagrange. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ThreePointPermutationClassBound
open PrimeIndexAbelianCentralizers PrimeIndexAbelianClassCount

private theorem third_point (i j : Fin 3) : ∃k : Fin 3,k≠i∧k≠j := by
  fin_cases i <;> fin_cases j <;> decide

theorem center_perm_three : Subgroup.center (Equiv.Perm (Fin 3))=⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply Equiv.ext
  intro i
  change g i=i
  by_contra hgi
  obtain ⟨k,hki,hkg⟩ := third_point i (g i)
  have he := congrArg (fun t : Equiv.Perm (Fin 3)=>t i)
    (Subgroup.mem_center_iff.mp hg (Equiv.swap i k))
  have hik : g i=g k := by
    simpa only [Equiv.Perm.mul_apply,Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hgi hkg.symm] using he
  exact hki (g.injective hik).symm

theorem centralKernel_eq_bot (N : Subgroup (Equiv.Perm (Fin 3))) : centralKernel N=⊥ := by
  apply le_antisymm _ bot_le
  intro n hn
  have he : (n:Equiv.Perm (Fin 3))=1 := by
    apply Subgroup.mem_bot.mp
    rw [←center_perm_three]
    exact hn
  exact Subgroup.mem_bot.mpr (Subtype.ext he)

theorem full_class_card : Nat.card (ConjClasses (Equiv.Perm (Fin 3)))=3 := by
  let N := alternatingGroup (Fin 3)
  have hN : Nat.card N=3 := by
    change Nat.card (alternatingGroup (Fin 3))=3
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : IsCyclic N := isCyclic_of_prime_card hN
  have hC : Nat.card (centralKernel N)=1 := by
    rw [centralKernel_eq_bot,Subgroup.card_bot]
  have hcount := prime_index_abelian_class_count N 2 Nat.prime_two
    (alternatingGroup.index_eq_two (α:=Fin 3))
  rw [hN,hC] at hcount
  omega

theorem subgroup_class_card_le_three (L : Subgroup (Equiv.Perm (Fin 3))) :
    Nat.card (ConjClasses L)≤3 := by
  by_cases hL : L=⊤
  · subst L
    have h := Nat.card_le_card_of_surjective
      (ConjClasses.map (Subgroup.topEquiv.symm.toMonoidHom :
        Equiv.Perm (Fin 3)→*(⊤:Subgroup (Equiv.Perm (Fin 3)))))
      (ConjClasses.map_surjective Subgroup.topEquiv.symm.surjective)
    rwa [full_class_card] at h
  · have hindex : 2≤L.index := L.one_lt_index_of_ne_top hL
    have hcard := L.card_mul_index
    have hperm : Nat.card (Equiv.Perm (Fin 3))=6 := by
      rw [Nat.card_perm,Nat.card_fin]
      rfl
    rw [hperm] at hcard
    have horder : Nat.card L≤3 := by
      nlinarith [Nat.mul_le_mul_left (Nat.card L) hindex]
    exact (Nat.card_le_card_of_surjective (@ConjClasses.mk L _) ConjClasses.mk_surjective).trans horder

end SymmetricSubgroupAsymptotics.ThreePointPermutationClassBound
