import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkZeroNormalRank
import SymmetricSubgroupAsymptotics.MarkedC4ProductColumns

/-! Ordinary generator cost of ONE global C4^r marking group. All source
subgroups are allowed, including vertical marking subgroups. The additional
ordinary rank is at most r; it is not multiplied by the physical factor count. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalMarkGeneratorRank
open ActualMarkZeroNormalRank

theorem genRank_le_of_surjective {G L : Type} [Group G] [Finite G] [Group L] [Finite L]
    (π : G →* L) (hπ : Function.Surjective π) : genRank L≤genRank G := by
  obtain ⟨S,hS,hgen⟩ := genRank_spec (G := G)
  have hc : Subgroup.closure (S.image π : Set L)=⊤ := by
    rw [Finset.coe_image,← MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective π hπ
  exact (genRank_le hc).trans (Finset.card_image_le.trans_eq hS)

abbrev Marks (r : ℕ) := Multiplicative (Fin r → ZMod 4)
theorem marks_binary (r : ℕ) : IsPGroup 2 (Marks r) := by
  apply IsPGroup.of_card (n := 2*r)
  rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  rw [show (4 : ℕ)=2^2 by norm_num,← pow_mul]

theorem subgroup_mark_rank_le (r : ℕ) (V : Subgroup (Marks r)) : genRank V≤r := by
  have h := (genRank_le_col_zero ((marks_binary r).to_subgroup V)).trans
    (col_zero_subgroup_le V)
  simpa [Marks,col_cyclicFourCoordinates] using h

variable {B : Type} [Group B] [Finite B] (r : ℕ) (A : Subgroup (B × Marks r))

def kernelMark : (physical A).ker →* Marks r := (mark A).comp (physical A).ker.subtype

theorem kernelMark_injective : Function.Injective (kernelMark r A) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hx : x.val.val.1=1 := x.property
    have hy : y.val.val.1=1 := y.property
    exact hx.trans hy.symm
  · exact he

/-- The global marker kernel is an ACTUAL subgroup of C4^r. -/
def kernelMarkEquiv : (physical A).ker ≃* (kernelMark r A).range :=
  MonoidHom.ofInjective (kernelMark_injective r A)

/-- Ordinary source rank plus r, derived from the exact physical-image
quotient and the single global marker kernel. -/
theorem genRank_le_physical_add_marks :
    genRank A≤genRank (PhysicalImage A)+r := by
  have hk : genRank (physical A).ker≤r :=
    (genRank_le_of_surjective (kernelMarkEquiv r A).symm.toMonoidHom
      (kernelMarkEquiv r A).symm.surjective).trans
        (subgroup_mark_rank_le r (kernelMark r A).range)
  let e := QuotientGroup.quotientKerEquivRange (physical A)
  have hq : genRank (A ⧸ (physical A).ker)≤genRank (PhysicalImage A) :=
    genRank_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  have h := genRank_le_of_normal (physical A).ker
  omega

end SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalMarkGeneratorRank
