import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive

/-! Actual point stabilizers in a transitive twelve-point group with
binary kernel and cubic quotient. Every stabilizer lies in the original
binary kernel and has index four there. No classification is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace SixPairB6CubicPointStabilizer
local instance cubicPointStabilizerPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {U : Subgroup (Equiv.Perm (Fin 12))}
    [MulAction.IsPretransitive U (Fin 12)]
    (top : U →* CyclicThree) (htop : Function.Surjective top)
    (hK : IsPGroup 2 top.ker)

include hK in
/-- A point stabilizer meeting C3 would make the binary kernel transitive
on twelve points, contradicting orbit-stabilizer divisibility. -/
theorem stabilizer_le_kernel (x : Fin 12) :
    MulAction.stabilizer U x ≤ top.ker := by
  by_contra hnot
  let H := MulAction.stabilizer U x
  have hs : Function.Surjective (top.comp H.subtype) := by
    letI : Fact (Nat.card CyclicThree).Prime := ⟨by
      norm_num [CyclicThree,Nat.card_eq_fintype_card]
      exact Nat.prime_three⟩
    apply MonoidHom.range_eq_top.mp
    apply (top.comp H.subtype).range.eq_bot_or_eq_top_of_prime_card.resolve_left
    intro hb
    apply hnot
    intro h hh
    apply MonoidHom.mem_ker.mpr
    have hm : top h ∈ (top.comp H.subtype).range := ⟨⟨h,hh⟩,rfl⟩
    rw [hb] at hm
    exact Subgroup.mem_bot.mp hm
  letI : MulAction.IsPretransitive top.ker (Fin 12) := by
    apply (MulAction.isPretransitive_iff_base (G := top.ker) x).mpr
    intro y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq U x y
    obtain ⟨h,hh⟩ := hs (top g)
    have hk : g*(h : U)⁻¹ ∈ top.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv]
      have hh' : top (h : U) = top g := hh
      rw [hh',mul_inv_cancel]
    refine ⟨⟨g*(h : U)⁻¹,hk⟩,?_⟩
    change (g*(h : U)⁻¹) • x = y
    rw [mul_smul]
    have hfix : (h : U)⁻¹ • x = x :=
      MulAction.mem_stabilizer_iff.mp (H.inv_mem h.2)
    rw [hfix]
    exact hg
  have hd : 12 ∣ Nat.card top.ker := by
    have h := (MulAction.stabilizer top.ker x).index_dvd_card
    simpa only [MulAction.index_stabilizer_of_transitive,Nat.card_fin] using h
  obtain ⟨a,ha⟩ := hK.exists_card_eq
  have hthree : 3 ∣ 2^a := (show 3 ∣ 12 by decide).trans (ha ▸ hd)
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
  norm_num at hbad

include htop hK in
/-- The SAME original stabilizer is a codimension-two subspace of the
actual elementary binary kernel once a vector chart is supplied. -/
theorem stabilizer_relative_index_four (x : Fin 12) :
    (MulAction.stabilizer U x).relIndex top.ker = 4 := by
  have h := Subgroup.relIndex_mul_index (stabilizer_le_kernel top hK x)
  have he : top.ker.index = 3 := by
    rw [Subgroup.index_ker,top.range_eq_top_of_surjective htop,Subgroup.card_top]
    norm_num [CyclicThree,Nat.card_eq_fintype_card]
  rw [he,MulAction.index_stabilizer_of_transitive,Nat.card_fin] at h
  omega

end SixPairB6CubicPointStabilizer
end SymmetricSubgroupAsymptotics
end
