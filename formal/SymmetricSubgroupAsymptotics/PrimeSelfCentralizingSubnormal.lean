import SymmetricSubgroupAsymptotics.SubnormalElementaryAbelianIrreducible
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A normal prime-order subgroup that contains its own centralizer
lies in every nontrivial subnormal subgroup. This uses the actual
subnormal chain, not a classification of subnormal subgroups. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimeSelfCentralizingSubnormal
open SubnormalElementaryAbelianIrreducible

variable {G : Type*} [Group G]

theorem irreducibleConjugation_of_prime_card
    (P N : Subgroup G) (hp : (Nat.card P).Prime) :
    IrreducibleConjugation N P := by
  letI : Fact (Nat.card P).Prime := ⟨hp⟩
  intro W hWP _
  rcases (W.subgroupOf P).eq_bot_or_eq_top_of_prime_card with hzero | hfull
  · left
    apply le_antisymm ?_ bot_le
    intro w hw
    have hmem : (⟨w,hWP hw⟩ : P) ∈ W.subgroupOf P := hw
    rw [hzero] at hmem
    exact Subgroup.mem_bot.mpr
      (congrArg (fun z : P => z.val) (Subgroup.mem_bot.mp hmem))
  · right
    exact le_antisymm hWP (Subgroup.subgroupOf_eq_top.mp hfull)

/-- The centralizing branch lies inside the prime subgroup; the
noncentral branch is the checked subnormal irreducibility argument. -/
theorem le_of_nontrivial_subnormal
    (P : Subgroup G) [P.Normal] (hp : (Nat.card P).Prime)
    (hself : Subgroup.centralizer (P : Set G) ≤ P)
    (N : Subgroup G) (hN : N.IsSubnormal) (hne : N ≠ ⊥) : P ≤ N := by
  by_cases hcentral : N ≤ Subgroup.centralizer (P : Set G)
  · have hNP : N ≤ P := hcentral.trans hself
    rcases irreducibleConjugation_of_prime_card P N hp N hNP N.le_normalizer with
      hzero | hfull
    · exact (hne hzero).elim
    · rw [hfull]
  · exact le_of_subnormal_irreducible_noncentral P N hN
      (irreducibleConjugation_of_prime_card P N hp) hcentral

end SymmetricSubgroupAsymptotics.PrimeSelfCentralizingSubnormal
