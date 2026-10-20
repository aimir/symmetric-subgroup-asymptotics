import SymmetricSubgroupAsymptotics.RelativeHeadAbelianSupplementCyclicCoverCompatible

/-! A cyclic quotient supplies a genuine cyclic supplement to an original
normal subgroup. The original abelianization cover bounds its relative head. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

 theorem relativeHead_le_two_of_cyclic_quotient_cyclicCover
    (p : ℕ) [Fact p.Prime]
    {G C D : Type} [Group G] [Finite G]
    [Group C] [Finite C] [IsCyclic C] [Group D] [Finite D] [IsCyclic D]
    (cover : C × D →* G ⧸ commutator G) (hcover : Function.Surjective cover)
    (M : Subgroup G) [M.Normal] [IsCyclic (G ⧸ M)] :
    Module.finrank (ZMod p) (primeRelativeCharacters p M)≤2 := by
  let q := QuotientGroup.mk' M
  obtain ⟨z,hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (G ⧸ M))
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective M z
  let K := Subgroup.zpowers g
  have hm : K.map q=⊤ := by
    change (Subgroup.zpowers g).map q=⊤
    rw [MonoidHom.map_zpowers,hg,hz]
  have hKM : K ⊔ M=⊤ := by
    have h := congrArg (Subgroup.comap q) hm
    rw [Subgroup.comap_map_eq,Subgroup.comap_top] at h
    change K ⊔ (QuotientGroup.mk' M).ker=⊤ at h
    simpa only [QuotientGroup.ker_mk'] using h
  have hK : IsMulCommutative K := inferInstance
  exact relativeHead_le_two_of_abelianSupplement_cyclicCover_compatible p cover hcover K M hKM hK
end SymmetricSubgroupAsymptotics
