import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Abelianization.Finite

/-! An actual abelian supplement identifies the full integral relative
commutator with the original derived subgroup. No mod-p head or exponent
assumption occurs. This retains possible higher cyclic factors exactly. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] (E A : Subgroup G) [E.Normal] [IsMulCommutative A]

/-- The SAME actual supplement and original normal subgroup. -/
theorem relative_commutator_eq_derived_of_abelian_supplement
    (hsup : E ⊔ A = ⊤) : ⁅E, (⊤ : Subgroup G)⁆ = commutator G := by
  let C := ⁅E, (⊤ : Subgroup G)⁆
  let q := QuotientGroup.mk' C
  have hcentral (e : G) (he : e ∈ E) : q e ∈ Subgroup.center (G ⧸ C) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hc : q ⁅e, g⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.commutator_mem_commutator he (Subgroup.mem_top g))
    rw [map_commutatorElement] at hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm
  let S : Set G := (E : Set G) ∪ (A : Set G)
  have hS : Subgroup.closure S = ⊤ := by
    simpa only [S, Subgroup.closure_union, Subgroup.closure_eq] using hsup
  have hcomm : IsMulCommutative (Subgroup.closure (q '' S)) :=
    Subgroup.isMulCommutative_closure (by
      rintro x ⟨e, he, rfl⟩ y ⟨a, ha, rfl⟩
      rcases he with he | he
      · exact ((Subgroup.mem_center_iff.mp (hcentral e he)) (q a)).symm
      · rcases ha with ha | ha
        · exact (Subgroup.mem_center_iff.mp (hcentral a ha)) (q e)
        · simpa only [map_mul] using congrArg q (setLike_mul_comm he ha))
  have htop : Subgroup.closure (q '' S) = ⊤ := by
    rw [← MonoidHom.map_closure, hS]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective C)
  rw [htop] at hcomm
  have hquot : IsMulCommutative (G ⧸ C) := ⟨⟨fun x y =>
    congrArg Subtype.val (hcomm.is_comm.comm
      (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup (G ⧸ C)))
      (⟨y, Subgroup.mem_top y⟩ : (⊤ : Subgroup (G ⧸ C))))⟩⟩
  apply le_antisymm
  · change ⁅E, (⊤ : Subgroup G)⁆ ≤ ⁅(⊤ : Subgroup G), ⊤⁆
    exact Subgroup.commutator_mono le_top le_rfl
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquot

/-- Exact INTEGRAL order accounting; no cyclic factor is reduced modulo p. -/
theorem relative_integral_order_mul_index_of_abelian_supplement [Finite G]
    (hsup : E ⊔ A = ⊤) :
    (⁅E, (⊤ : Subgroup G)⁆).relIndex E * E.index = Nat.card (Abelianization G) := by
  have heq := relative_commutator_eq_derived_of_abelian_supplement E A hsup
  have hle : commutator G ≤ E := by
    rw [← heq]
    exact Subgroup.commutator_le_left E (⊤ : Subgroup G)
  have h := Subgroup.relIndex_mul_index hle
  change (commutator G).relIndex E * E.index = Nat.card (Abelianization G) at h
  simpa only [heq] using h

end SymmetricSubgroupAsymptotics
