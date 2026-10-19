import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopLinearSocles
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.SingleCubicBinaryResidual

/-! An actual elementary-binary extension of a faithful A4/S4 quartet
image has exactly one cubic factor in its order. Cauchy's theorem gives
an ACTUAL order-three subgroup for the retained binary separator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOrder
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)

theorem linear_card (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    Nat.card C=12 ∨ Nat.card C=24 := by
  let E : C ≃* (top C).range := MulEquiv.ofBijective (top C).rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h),(top C).rangeRestrict_surjective⟩
  have ht : alternatingGroup (Fin 4)≤(top C).range := by
    intro p hp
    exact heven ⟨p,hp⟩
  rcases AlternatingTopImageNormalGenerators.above_alternating (top C).range ht with h | h
  · left
    rw [Nat.card_congr E.toEquiv,h]
    exact alternatingGroup.card_of_card_eq_four (by simp)
  · right
    rw [Nat.card_congr E.toEquiv,h,Nat.card_congr Subgroup.topEquiv.toEquiv]
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    norm_num

theorem exists_single_cubic_order {G : Type} [Group G] [Finite G]
    (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (pi : G →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) [Finite A]
    (E : OriginalKernelModuleChart pi A) : ∃ k : ℕ, Nat.card G=3*2^k := by
  have hk : Nat.card pi.ker=2^Module.finrank (ZMod 2) A := by
    rw [← Nat.card_congr E.equiv.toEquiv]
    change Nat.card A=2^Module.finrank (ZMod 2) A
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hp := pi.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hpi,
    Nat.card_congr Subgroup.topEquiv.toEquiv,hk] at hp
  rcases linear_card C hinj heven with hc | hc
  · refine ⟨Module.finrank (ZMod 2) A+2,?_⟩
    rw [hc] at hp
    rw [← hp,pow_add]
    norm_num <;> ring
  · refine ⟨Module.finrank (ZMod 2) A+3,?_⟩
    rw [hc] at hp
    rw [← hp,pow_add]
    norm_num <;> ring

theorem exists_actual_cubic_subgroup {G : Type} [Group G] [Finite G]
    (k : ℕ) (hG : Nat.card G=3*2^k) : ∃ P : Subgroup G, Nat.card P=3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : 3∣Nat.card G := by rw [hG]; exact dvd_mul_right _ _
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 hd
  exact ⟨Subgroup.zpowers g,by rw [Nat.card_zpowers,hg]⟩

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalOrder
