import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExtension
import Mathlib.GroupTheory.Abelianization.Finite

/-! Actual full integral coinvariants embed into the centre after killing
exactly their ambient mixed commutator. A previously proved quotient-centre
bound can therefore control them without discarding cyclic factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G] [Finite G]

theorem normalIntegralCoinvariantOrder_le_mixed_quotient_center
    (N : Subgroup G) [N.Normal] :
    normalIntegralCoinvariantOrder N≤Nat.card (Subgroup.center (G ⧸ ⁅N,(⊤ : Subgroup G)⁆)) := by
  let C := ⁅N,(⊤ : Subgroup G)⁆
  let q := QuotientGroup.mk' C
  have hcentral : N.map q≤Subgroup.center (G ⧸ C) := by
    rintro x ⟨n,hn,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C y
    have hc : q ⁅n,g⁆=1 := (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.commutator_mem_commutator hn (Subgroup.mem_top g))
    rw [map_commutatorElement] at hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm
  have he := Subgroup.relIndex_ker N q
  rw [QuotientGroup.ker_mk'] at he
  exact he.trans_le (Subgroup.card_le_of_le hcentral)

/-- The abelian branch retains the full abelianization order. The
nonabelian branch uses the centre bound on the SAME mixed quotient. -/
theorem normalIntegralCoinvariantOrder_le_of_quotient_center_bound
    (N : Subgroup G) [N.Normal] (b : ℕ)
    (hAb : Nat.card (Abelianization G)≤b*N.index)
    (hcentres : ∀ C : Subgroup G,∀ [C.Normal],
      (¬∀ x y : G ⧸ C,x*y=y*x) → Nat.card (Subgroup.center (G ⧸ C))≤b) :
    normalIntegralCoinvariantOrder N≤b := by
  let C := ⁅N,(⊤ : Subgroup G)⁆
  by_cases hnon : ¬∀ x y : G ⧸ C,x*y=y*x
  · exact (normalIntegralCoinvariantOrder_le_mixed_quotient_center N).trans (hcentres C hnon)
  · have hcomm : IsMulCommutative (G ⧸ C) := ⟨⟨not_not.mp hnon⟩⟩
    have hCD : C=commutator G := by
      apply le_antisymm
      · exact Subgroup.commutator_mono le_top le_rfl
      · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
    have hDN : commutator G≤N := by
      rw [←hCD]
      exact Subgroup.commutator_le_left N ⊤
    have he := Subgroup.relIndex_mul_index hDN
    change (commutator G).relIndex N*N.index=Nat.card (Abelianization G) at he
    have hs : normalIntegralCoinvariantOrder N*N.index=Nat.card (Abelianization G) := by
      change C.relIndex N*N.index=_
      rw [hCD]
      exact he
    have hm : normalIntegralCoinvariantOrder N*N.index≤b*N.index := hs.le.trans hAb
    exact Nat.le_of_mul_le_mul_right hm (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
end SymmetricSubgroupAsymptotics
