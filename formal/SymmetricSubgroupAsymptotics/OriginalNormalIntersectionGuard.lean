import SymmetricSubgroupAsymptotics.BinaryCoverage
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Recovering the whole original normal subgroup from a center bound.

The image of N in G/L is not discarded. When L=N∩K and the whole center
of G/L lies in the image of K, the actual binary normal-center theorem
forces that image of N to be trivial. Thus N=L is a conclusion.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup disjoint from a subgroup containing the whole
center of a finite binary group is trivial. -/
theorem binary_normal_eq_bot_of_center_le
    (hG : IsPGroup 2 G) (N K : Subgroup G) [N.Normal]
    (hcenter : Subgroup.center G≤K) (hdisjoint : N⊓K=⊥) : N=⊥ := by
  by_contra hN
  obtain ⟨z,hzN,hzc,hzo⟩ := pGroup_normal_contains_central_prime hG N hN
  have hz : z∈N⊓K := ⟨hzN,hcenter hzc⟩
  rw [hdisjoint,Subgroup.mem_bot] at hz
  rw [hz,orderOf_one] at hzo
  exact (by decide : (1:ℕ)≠2) hzo

/-- The literal image of N/L meets K/L trivially, and hence vanishes,
once the center of the actual quotient is contained in K/L. -/
theorem original_normal_eq_intersection_of_quotient_center_le
    (hG : IsPGroup 2 G) (N K L : Subgroup G) [N.Normal] [L.Normal]
    (hLN : L≤N) (hLK : L≤K) (hintersection : N⊓K≤L)
    (hcenter : Subgroup.center (G ⧸ L)≤K.map (QuotientGroup.mk' L)) :
    N=L := by
  let q := QuotientGroup.mk' L
  have hdisjoint : N.map q⊓K.map q=⊥ := by
    apply le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨n,hn,rfl⟩ := hz.1
    have hnK : n∈K := by
      have hcomap : n∈(K.map q).comap q := hz.2
      have hker : q.ker≤K := by
        simpa only [q,QuotientGroup.ker_mk'] using hLK
      rw [Subgroup.comap_map_eq_self hker] at hcomap
      exact hcomap
    change q n=1
    exact (QuotientGroup.eq_one_iff n).mpr (hintersection ⟨hn,hnK⟩)
  have himage : N.map q=⊥ :=
    binary_normal_eq_bot_of_center_le (hG.to_quotient L)
      (N.map q) (K.map q) hcenter hdisjoint
  apply le_antisymm ?_ hLN
  have hNker := (Subgroup.map_eq_bot_iff (H := N)).mp himage
  simpa only [q,QuotientGroup.ker_mk'] using hNker

end SymmetricSubgroupAsymptotics
