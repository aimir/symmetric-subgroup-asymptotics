import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! A literal product of two soluble subgroups is soluble when the second
normalizes the first. The containing subgroup and product witnesses remain
actual elements; no cardinal or recognition assumption is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSolubleNormalizerProduct
variable {G : Type*} [Group G]

theorem soluble_of_product_cover (N B W : Subgroup G)
    (hB : B≤N) (hW : W≤N)
    (hn : W≤Subgroup.normalizer (B : Set G))
    (hcover : ∀x∈N,∃b∈B,∃w∈W,b*w=x)
    [IsSolvable B] [IsSolvable W] : IsSolvable N := by
  let B₀ := B.subgroupOf N
  have hNB : N≤Subgroup.normalizer (B : Set G) := by
    intro x hx
    obtain ⟨b,hb,w,hw,rfl⟩ := hcover x hx
    exact (Subgroup.normalizer (B : Set G)).mul_mem (B.le_normalizer hb) (hn hw)
  letI : B₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hB).mpr hNB
  letI : IsSolvable B₀ := solvable_of_solvable_injective
    (f:=(Subgroup.subgroupOfEquivOfLe hB).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hB).injective
  let q : N→*N⧸B₀ := QuotientGroup.mk' B₀
  let f : W→*N⧸B₀ := q.comp (Subgroup.inclusion hW)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective B₀ y
    obtain ⟨b,hb,w,hw,hbw⟩ := hcover x.val x.property
    have hx : x=(⟨b,hB hb⟩:N)*(⟨w,hW hw⟩:N) := Subtype.ext hbw.symm
    refine ⟨⟨w,hw⟩,?_⟩
    change q ⟨w,hW hw⟩=q x
    rw [hx,map_mul]
    have hbq : q (⟨b,hB hb⟩:N)=1 := (QuotientGroup.eq_one_iff _).mpr hb
    rw [hbq,one_mul]
  letI : IsSolvable (N⧸B₀) := solvable_of_surjective (f:=f) hf
  exact solvable_of_ker_le_range B₀.subtype q (by
    change (QuotientGroup.mk' B₀).ker≤B₀.subtype.range
    rw [QuotientGroup.ker_mk',Subgroup.range_subtype])

end SymmetricSubgroupAsymptotics.CFSGSolubleNormalizerProduct
