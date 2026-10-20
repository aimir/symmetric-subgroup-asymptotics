import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairFrameSource

/-! Trivial actual translation centralizer implies fixed-freeness of the
unchanged original elementary kernel representation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem degreeFourCubicCentralizer_fixedFree
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (S : Sylow 3 (preE7NonPairAction w U)) (s : preE7NonPairAction w U)
    (hgen : (S : Subgroup (preE7NonPairAction w U)) = Subgroup.zpowers s)
    (hzero : ∀ e : preE7NonPairAction w U, e ∈ E block P →
      (∀ t : preE7NonPairAction w U, t ∈ (S : Subgroup (preE7NonPairAction w U)) →
        e*t=t*e) → e=1) :
    ∀ v : (elementaryChart block P).V,
      (elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) s) v=v → v=0 := by
  intro v hv
  let C := elementaryChart block P
  let e : E block P := C.equiv.symm (Multiplicative.ofAdd v)
  have he : MulAut.conjNormal s e=e := by
    apply C.equiv.injective
    apply Multiplicative.toAdd.injective
    have h := C.quotientRepresentation_apply s e
    have hev : (C.equiv e).toAdd=v := by
      change (C.equiv (C.equiv.symm (Multiplicative.ofAdd v))).toAdd=v
      rw [C.equiv.apply_symm_apply]
      rfl
    rw [hev] at h
    exact h.symm.trans (hv.trans hev.symm)
  have hcomm : Commute (e : preE7NonPairAction w U) s := by
    have h : s*(e : preE7NonPairAction w U)*s⁻¹=(e : preE7NonPairAction w U) :=
      congrArg Subtype.val he
    exact ((mul_inv_eq_iff_eq_mul).mp h).symm
  have he1 : (e : preE7NonPairAction w U)=1 := by
    apply hzero e e.2
    intro t ht
    rw [hgen] at ht
    obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    exact hcomm.zpow_right k
  have he0 : e=1 := Subtype.ext he1
  have hv0 : C.equiv e=1 := by rw [he0,map_one]
  change C.equiv (C.equiv.symm (Multiplicative.ofAdd v))=1 at hv0
  rw [C.equiv.apply_symm_apply] at hv0
  exact congrArg Multiplicative.toAdd hv0

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
