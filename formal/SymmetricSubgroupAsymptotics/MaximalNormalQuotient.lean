import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Order.Preorder.Finite

/-! Maximal proper normal subgroups and their actual simple quotients.
These quotient-correspondence arguments are independent of the induced
representation and minimal-normal-subgroup constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

section Quotient
variable (G : Type*) [Group G] [Finite G] [Nontrivial G]

theorem finite_exists_maximal_normal :
    ∃ M : Subgroup G, M.Normal ∧ M≠⊤ ∧
      ∀ K : Subgroup G, K.Normal → M≤K → K=M ∨ K=⊤ := by
  classical
  let s : Set (Subgroup G) := {M | M.Normal ∧ M≠⊤}
  obtain ⟨M,hM,hmax⟩ := s.toFinite.exists_maximal (show s.Nonempty from
    ⟨⊥,inferInstance,bot_ne_top⟩)
  refine ⟨M,hM.1,hM.2,?_⟩
  intro K hK hMK
  by_cases he : K=⊤
  · exact Or.inr he
  · exact Or.inl (le_antisymm (hmax ⟨hK,he⟩ hMK) hMK)

omit [Finite G] [Nontrivial G] in
theorem maximal_normal_quotient_simple (M : Subgroup G) [M.Normal] (hM : M≠⊤)
    (hmax : ∀ K : Subgroup G, K.Normal → M≤K → K=M ∨ K=⊤) :
    IsSimpleGroup (G⧸M) := by
  letI : Nontrivial (G⧸M) := QuotientGroup.nontrivial_iff.mpr hM
  constructor
  intro L hL
  let π := QuotientGroup.mk' M
  have hs : Function.Surjective π := QuotientGroup.mk'_surjective M
  have hle : M≤L.comap π := by
    intro x hx
    change π x∈L
    have hπ : π x=1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hπ]
    exact L.one_mem
  rcases hmax (L.comap π) (hL.comap π) hle with he|he
  · left
    apply Subgroup.comap_injective hs
    simpa only [MonoidHom.comap_bot,π,QuotientGroup.ker_mk'] using he
  · right
    apply Subgroup.comap_injective hs
    simpa only [Subgroup.comap_top] using he

end Quotient

end SymmetricSubgroupAsymptotics
