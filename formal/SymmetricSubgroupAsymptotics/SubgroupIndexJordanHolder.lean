import SymmetricSubgroupAsymptotics.MaximalNormalQuotient
import Mathlib.GroupTheory.Index
import Mathlib.Order.JordanHolder

/-! The Jordan–Hölder lattice axioms for actual subgroup inclusions,
retaining the orders of their simple quotients. The pair relation is
equality of relative indices; no abstract composition-factor invariance
is assumed. This weaker relation is enough to count factors of order
three in any two actual composition series. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G]

/-- A proper maximal normal inclusion in its actual upper subgroup. -/
structure NormalCompositionCover (H K : Subgroup G) : Prop where
  lt : H < K
  normal : (H.subgroupOf K).Normal
  maximal : ∀ M : Subgroup K, M.Normal → H.subgroupOf K ≤ M →
    M = H.subgroupOf K ∨ M = ⊤

namespace NormalCompositionCover

theorem quotient_simple {H K : Subgroup G} (h : NormalCompositionCover H K) :
    letI := h.normal
    IsSimpleGroup (K ⧸ H.subgroupOf K) := by
  letI := h.normal
  apply maximal_normal_quotient_simple K (H.subgroupOf K)
  · exact fun he => (not_le_of_gt h.lt) (Subgroup.subgroupOf_eq_top.mp he)
  · exact h.maximal

theorem of_simple {H K : Subgroup G} (hlt : H < K)
    [hn : (H.subgroupOf K).Normal] [IsSimpleGroup (K ⧸ H.subgroupOf K)] :
    NormalCompositionCover H K := by
  refine ⟨hlt, hn, ?_⟩
  intro M hM hHM
  let π := QuotientGroup.mk' (H.subgroupOf K)
  letI := hM
  have hker : π.ker ≤ M := by simpa only [π, QuotientGroup.ker_mk'] using hHM
  have he : (M.map π).comap π = M := Subgroup.comap_map_eq_self hker
  rcases (inferInstance : (M.map π).Normal).eq_bot_or_eq_top with hb | ht
  · left
    rw [hb, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at he
    exact he.symm
  · right
    rw [ht, Subgroup.comap_top] at he
    exact he.symm

theorem sup_eq {H K L : Subgroup G}
    (hH : NormalCompositionCover H L) (hK : NormalCompositionCover K L)
    (hne : H ≠ K) : H ⊔ K = L := by
  letI := hH.normal
  letI := hK.normal
  rcases hH.maximal (H.subgroupOf L ⊔ K.subgroupOf L) inferInstance le_sup_left with he | he
  · have hKH : K ≤ H := by
      intro x hx
      exact (le_sup_right.trans_eq he) (show (⟨x, hK.lt.le hx⟩ : L) ∈ K.subgroupOf L from hx)
    rcases hK.maximal (H.subgroupOf L) hH.normal
      (fun x hx => hKH hx) with he' | he'
    · apply False.elim
      apply hne
      have hm := congrArg (Subgroup.map L.subtype) he'
      simpa only [Subgroup.map_subgroupOf_eq_of_le hH.lt.le,
        Subgroup.map_subgroupOf_eq_of_le hK.lt.le] using hm
    · exact False.elim ((not_le_of_gt hH.lt) (Subgroup.subgroupOf_eq_top.mp he'))
  · rw [← Subgroup.subgroupOf_sup hH.lt.le hK.lt.le] at he
    exact le_antisymm (sup_le hH.lt.le hK.lt.le) (Subgroup.subgroupOf_eq_top.mp he)

theorem inf_left {H K : Subgroup G}
    (hK : NormalCompositionCover K (H ⊔ K)) :
    NormalCompositionCover (H ⊓ K) H := by
  have hnorm : H ≤ Subgroup.normalizer (K : Set G) := le_sup_left.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp hK.normal)
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  letI := hK.quotient_simple
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hnorm
  letI : IsSimpleGroup (H ⧸ K.subgroupOf H) := e.isSimpleGroup
  have hi : (H ⊓ K).subgroupOf H = K.subgroupOf H := by
    rw [inf_comm, Subgroup.inf_subgroupOf_right]
  have hlt : H ⊓ K < H := lt_of_le_of_ne inf_le_left (by
    intro he
    have hHK : H ≤ K := he.symm.le.trans inf_le_right
    exact hK.lt.ne (sup_of_le_right hHK).symm)
  have hn : ((H ⊓ K).subgroupOf H).Normal := hi.symm ▸ inferInstance
  letI := hn
  have hs : IsSimpleGroup (H ⧸ (H ⊓ K).subgroupOf H) := by
    exact (QuotientGroup.quotientMulEquivOfEq hi).isSimpleGroup
  letI := hs
  exact of_simple hlt

theorem second_index {H K : Subgroup G}
    (hH : NormalCompositionCover H (H ⊔ K)) :
    H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hnorm : K ≤ Subgroup.normalizer (H : Set G) := le_sup_right.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hH.normal)
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have he := Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient K H hnorm).toEquiv
  have hi : H.relIndex K = H.relIndex (K ⊔ H) := by
    simpa only [Subgroup.relIndex, Subgroup.index_eq_card] using he
  rw [Subgroup.inf_relIndex_right, sup_comm]
  exact hi.symm

end NormalCompositionCover

/-- This local instance records quotient orders, which suffice for the
prime-factor multiplicities used by the chosen-chief-weight bound. -/
@[reducible] def subgroupIndexJordanHolder (G : Type*) [Group G] :
    JordanHolderLattice (Subgroup G) where
  IsMaximal := NormalCompositionCover
  lt_of_isMaximal h := h.lt
  sup_eq_of_isMaximal := NormalCompositionCover.sup_eq
  isMaximal_inf_left_of_isMaximal_sup _ hK := NormalCompositionCover.inf_left hK
  Iso x y := x.1.relIndex x.2 = y.1.relIndex y.2
  iso_symm h := h.symm
  iso_trans h h' := h.trans h'
  second_iso := NormalCompositionCover.second_index

end SymmetricSubgroupAsymptotics
