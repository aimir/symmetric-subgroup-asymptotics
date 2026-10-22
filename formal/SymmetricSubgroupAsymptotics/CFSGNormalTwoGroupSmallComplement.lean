import SymmetricSubgroupAsymptotics.CFSGPermutationNormalRestriction
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card

/-! A normal two-subgroup of a symmetric group on at least five points
is trivial. Restriction to an invariant subset with at most one outside
point is faithful, so the same conclusion applies to the original group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupSmallComplement
open Equiv Equiv.Perm CFSGPermutationNormalRestriction CFSGPermutationSubsetProduct

theorem normal_two_subgroup_eq_bot {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H : Subgroup (Perm Y)) (hH : IsPGroup 2 H) (hN : H.Normal)
    (hsize : 5 ≤ Nat.card Y) : H = ⊥ := by
  by_contra hne
  letI : H.Normal := hN
  letI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hne
  have hAlt : alternatingGroup Y ≤ H := alternatingGroup_le_of_normal hsize inferInstance
  have hthree : 2 < (Set.univ : Set Y).ncard := by
    simpa only [Set.ncard_univ] using (show 2 < Nat.card Y by omega)
  rw [Set.two_lt_ncard_iff] at hthree
  obtain ⟨a, b, c, _, _, _, hab, hac, hbc⟩ := hthree
  let t : Perm Y := Equiv.swap a b * Equiv.swap a c
  have ht : IsThreeCycle t := isThreeCycle_swap_mul_swap_same hab hac hbc
  let u : H := ⟨t, hAlt ht.mem_alternatingGroup⟩
  have hu : orderOf u = 3 := by rw [Subgroup.orderOf_mk]; exact ht.orderOf
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hH) u
  have hd : 3 ∣ 2 ^ n := by rw [← hn, hu]
  exact (by decide : (3 : ℕ) ≠ 2)
    (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two hd)

theorem restrictionHom_injective_of_small_complement
    {X : Type*} [DecidableEq X] (P : Subgroup (Perm X)) (s : Set X)
    (hPs : P ≤ MulAction.stabilizer (Perm X) s) (hcompl : (sᶜ : Set X).Subsingleton) :
    Function.Injective (restrictionHom P s hPs) := by
  intro a b hab
  apply Subtype.ext
  apply Perm.ext
  intro x
  by_cases hx : x ∈ s
  · exact congrArg (fun q : Perm s => (q ⟨x, hx⟩).val) hab
  · have ha : a.val x ∈ sᶜ := by
      intro h
      exact hx ((MulAction.mem_stabilizer_set.mp (hPs a.property) x).mp h)
    have hb : b.val x ∈ sᶜ := by
      intro h
      exact hx ((MulAction.mem_stabilizer_set.mp (hPs b.property) x).mp h)
    exact hcompl ha hb

theorem eq_bot_of_normal_restriction {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hP : IsPGroup 2 P) (s : Set X)
    (hPs : P ≤ MulAction.stabilizer (Perm X) s) (hsize : 5 ≤ Nat.card s)
    (hcompl : (sᶜ : Set X).Subsingleton)
    (hN : ∀ t : Perm s, splitEmbedding s (t, 1) ∈ Subgroup.normalizer (P : Set (Perm X))) :
    P = ⊥ := by
  let rho := restrictionHom P s hPs
  have hR : IsPGroup 2 rho.range :=
    hP.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
  have hbot : rho.range = ⊥ := normal_two_subgroup_eq_bot rho.range hR
    (restriction_range_normal P s hPs hN) hsize
  have hinj := restrictionHom_injective_of_small_complement P s hPs hcompl
  apply bot_unique
  intro x hx
  change x = 1
  have hr : rho ⟨x, hx⟩ = 1 := by
    have hm : rho ⟨x, hx⟩ ∈ rho.range := ⟨⟨x, hx⟩, rfl⟩
    rw [hbot] at hm
    exact hm
  have he : (⟨x, hx⟩ : P) = 1 := hinj (by simpa only [map_one] using hr)
  exact congrArg Subtype.val he

end SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupSmallComplement
