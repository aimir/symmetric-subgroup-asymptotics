import SymmetricSubgroupAsymptotics.BinaryCoverage
import SymmetricSubgroupAsymptotics.MonolithicSelfCentralizingKernelNormalCover

/-! A literal two-element centralizer certificate replaces a normal census.
The p-group kernel and its centralizer remain in the original group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

 theorem normal_cover_of_binary_kernel_centralizer
    {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hK : IsPGroup 2 K)
    (z : G) (hzK : z∈K)
    (hc : ∀ x : G, x∈Subgroup.centralizer (K : Set G) → x=1 ∨ x=z)
    (N : Subgroup G) (hN : N.Normal) (hne : N≠⊥) : Subgroup.zpowers z≤N := by
  have hcentralizer : Subgroup.centralizer (K : Set G)≤K := by
    intro x hx
    rcases hc x hx with rfl | rfl
    · exact K.one_mem
    · exact hzK
  apply normal_cover_of_selfCentralizing_monolith K (Subgroup.zpowers z)
    hcentralizer ?_ N hN hne
  intro H hHnormal hHK hH
  letI : H.Normal := hHnormal
  have hHKne : H.subgroupOf K≠⊥ := by
    intro hb
    apply hH
    apply le_antisymm _ bot_le
    intro x hx
    have hh : (⟨x,hHK hx⟩ : K)∈H.subgroupOf K := hx
    rw [hb] at hh
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hh)
  obtain ⟨x,hxH,hxc,hxo⟩ :=
    pGroup_normal_contains_central_prime hK (H.subgroupOf K) hHKne
  have hxne : (x : G)≠1 := by
    intro he
    have hxone : x=1 := Subtype.ext he
    have : (2 : ℕ)=1 := by simpa only [hxone,orderOf_one] using hxo.symm
    omega
  have hxcentral : (x : G)∈Subgroup.centralizer (K : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc (⟨k,hk⟩ : K))
  have hxz : (x : G)=z := (hc x hxcentral).resolve_left hxne
  apply Subgroup.zpowers_le.mpr
  change (x : G)∈H at hxH
  exact hxz ▸ hxH

end SymmetricSubgroupAsymptotics
