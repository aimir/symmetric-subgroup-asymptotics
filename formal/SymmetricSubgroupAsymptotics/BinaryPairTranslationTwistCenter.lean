import SymmetricSubgroupAsymptotics.BinaryPairAffineCommutator
import SymmetricSubgroupAsymptotics.BinaryFourTranslationMoments
import SymmetricSubgroupAsymptotics.OriginalNormalIntersectionGuard

/-! Nonzero parity in an exact original regular-coordinate chart.

The central commutator is derived in U/(N∩ker(top)), then projected through
the literal first-block moment. A nonzero parity character excludes every
central top translation. Only afterwards does the binary normal-center
theorem force the whole original N into the pair kernel.

The chart hypotheses are explicit: they must be supplied by the actual
two-regular-orbit chart. In particular this module does not classify
zero twists, identify split carriers, or assume N=N∩ker(top).
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryTranslationMoments

variable {X I V : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem normalSpace_inf_top_kernel :
    F.normalSpace (N⊓F.top.ker)=F.normalSpace N := by
  have h : (N⊓F.top.ker).subgroupOf F.top.ker=N.subgroupOf F.top.ker := by
    ext k
    change ((k:U)∈N ∧ (k:U)∈F.top.ker) ↔ (k:U)∈N
    exact and_iff_left k.property
  unfold normalSpace
  rw [h]

variable (H : Subgroup F.top.range) (e : V ⊕ V ≃ I)
    (coordinate : H → V) (hcoordinate : Function.Surjective coordinate)
    (hV : Nat.card V=4)
    (haction : ∀ h : H,∀ v,
      (h:F.top.range).val (e (Sum.inl v))=e (Sum.inl (coordinate h+v)))
    (hcentralChart : ∀ t : F.top.range,t∈Subgroup.center F.top.range →
      ∃ δ : V,
        (∀ v,t.val (e (Sum.inl v))=e (Sum.inl (δ+v))) ∧
        (∀ v,t.val (e (Sum.inr v))=e (Sum.inr (δ+v))))
    (hlower : ∀ f∈(F.normalSpace N).map F.kernelSpace.subtype,∀ v,
      f (e (Sum.inl v))=f (e (Sum.inl 0)))
    (hparity : ∃ h : H,
      BinaryTranslationMoments.parity (leftFunction e (F.affineTranslation (F.affineTopLift h)))≠0)

include hcoordinate hV haction hcentralChart hlower hparity in
/-- Every central class of the actual intermediate quotient has trivial
original top. Its affine commutator equations are proved, not supplied. -/
theorem central_intersection_quotient_mem_top_kernel
    (u : U)
    (hu : QuotientGroup.mk' (N⊓F.top.ker) u∈
      Subgroup.center (U ⧸ (N⊓F.top.ker))) : u∈F.top.ker := by
  let S := N⊓F.top.ker
  have hS : S≤F.top.rangeRestrict.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    exact Subtype.ext ha.2
  let π := QuotientGroup.lift S F.top.rangeRestrict hS
  have htc : F.top.rangeRestrict u∈Subgroup.center F.top.range := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨v,rfl⟩ := F.top.rangeRestrict_surjective t
    have hq : QuotientGroup.mk' S (v*u)=QuotientGroup.mk' S (u*v) := by
      simpa only [map_mul] using
        (Subgroup.mem_center_iff.mp hu (QuotientGroup.mk' S v))
    have he := congrArg π hq
    change F.top.rangeRestrict (v*u)=F.top.rangeRestrict (u*v) at he
    simpa only [map_mul] using he
  obtain ⟨δ,hδ₁,hδ₂⟩ := hcentralChart (F.top.rangeRestrict u) htc
  let χ : H → ZMod 2 := fun h =>
    BinaryTranslationMoments.parity (leftFunction e (F.affineTranslation (F.affineTopLift h)))
  let p : ZMod 2 := BinaryTranslationMoments.parity (leftFunction e (F.affineTranslation u))
  have hcomm (h : H) : χ h • δ+p • coordinate h=0 := by
    let v := F.affineTopLift (h:F.top.range)
    have hv : F.top.rangeRestrict v=(h:F.top.range) := F.affineTopLift_top h
    have hvact : ∀ x,F.top v (e (Sum.inl x))=e (Sum.inl (coordinate h+x)) := by
      intro x
      change (F.top.rangeRestrict v).val (e (Sum.inl x))=_
      rw [hv]
      exact haction h x
    have hm := F.affine_commutator_mem_normalSpace_of_le_kernel S inf_le_right u v hu
    change _∈(F.normalSpace (N⊓F.top.ker)).map F.kernelSpace.subtype at hm
    rw [F.normalSpace_inf_top_kernel N] at hm
    have hz := left_moment_eq_zero_of_constant hV e _ (hlower _ hm)
    have he := left_commutator_moment e (F.top u) (F.top v) δ (coordinate h)
      hδ₁ hvact (F.affineTranslation u) (F.affineTranslation v)
    change moment (leftFunction e
      ((fun x => F.affineTranslation v ((F.top u)⁻¹ x))+F.affineTranslation u-
      ((fun x => F.affineTranslation u ((F.top v)⁻¹ x))+F.affineTranslation v)))=0 at hz
    exact he.symm.trans hz
  have hδ : δ=0 := translation_eq_zero_of_nonzero_parity coordinate hcoordinate χ
    hparity (by rw [hV]; decide) δ p hcomm
  change F.top u=1
  apply Equiv.ext
  intro x
  obtain ⟨z,rfl⟩ := e.surjective x
  cases z with
  | inl v => simpa only [hδ,zero_add,Equiv.Perm.one_apply] using hδ₁ v
  | inr v => simpa only [hδ,zero_add,Equiv.Perm.one_apply] using hδ₂ v

include hcoordinate hV haction hcentralChart hlower hparity in
/-- The whole original normal subgroup is recovered only after the
proved center exclusion. No quotient-monotonicity of central rank is
used, and no original top image of N is discarded. -/
theorem original_normal_eq_intersection_of_nonzero_translation_parity
    [Finite X] (hU : IsPGroup 2 U) : N=N⊓F.top.ker := by
  apply original_normal_eq_intersection_of_quotient_center_le hU
    N F.top.ker (N⊓F.top.ker) inf_le_left inf_le_right le_rfl
  intro z hz
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (N⊓F.top.ker) z
  exact ⟨u,F.central_intersection_quotient_mem_top_kernel N H e coordinate hcoordinate
    hV haction hcentralChart hlower hparity u hz,rfl⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
