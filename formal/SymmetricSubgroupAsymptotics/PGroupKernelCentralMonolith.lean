import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import SymmetricSubgroupAsymptotics.BinaryCoverage
import SymmetricSubgroupAsymptotics.MonolithicSelfCentralizingKernelNormalCover

/-! A minimal normal containing the center of a normal p-group kernel is
its ambient monolith when the kernel is self-centralizing. The center need
not be pointwise fixed by the ambient group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

 theorem normal_cover_of_pGroup_kernel_central_monolith
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (K D : Subgroup G) [K.Normal]
    (hK : IsPGroup p K)
    (hcentralizer : Subgroup.centralizer (K : Set G)≤K)
    (hcenter : ∀ x : K, x∈Subgroup.center K → (x : G)∈D)
    (hD : IsMinimalNormalSubgroup D)
    (N : Subgroup G) (hN : N.Normal) (hne : N≠⊥) : D≤N := by
  letI : D.Normal := hD.1
  apply normal_cover_of_selfCentralizing_monolith K D hcentralizer ?_ N hN hne
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
    exact (Fact.out : p.Prime).ne_one (by
      simpa only [hxone,orderOf_one] using hxo.symm)
  have hmeet : H⊓D≠⊥ := by
    intro hb
    have hh : (x : G)∈H⊓D := ⟨hxH,hcenter x hxc⟩
    rw [hb] at hh
    exact hxne (Subgroup.mem_bot.mp hh)
  have he : H⊓D=D := hD.2.2 (H⊓D) inferInstance hmeet inf_le_right
  exact he.symm.le.trans inf_le_left

end SymmetricSubgroupAsymptotics
