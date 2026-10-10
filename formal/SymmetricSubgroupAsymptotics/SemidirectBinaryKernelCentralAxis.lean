import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignCentralSeries

/-!
# Central binary axes in split extensions

Suppose an epimorphism of semidirect products is an isomorphism on the
normal factor and has binary kernel of order at most four on the acting
factor.  A central order-two subgroup of the latter kernel acts trivially
on the normal factor, so its copy in the full semidirect product is central.

This is the reusable bridge needed for ternary-by-binary sections: the
ambient group itself need not be a 2-group.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A chosen central order-two subgroup inside the kernel of a map. -/
structure CentralOrderTwoKernelAxis
    {G Q : Type*} [Group G] [Group Q] (pi : G →* Q) where
  C : Subgroup G
  [normalC : C.Normal]
  C_le_kernel : C ≤ pi.ker
  C_card : Nat.card C = 2
  C_le_center : C ≤ Subgroup.center G

attribute [instance] CentralOrderTwoKernelAxis.normalC

namespace CentralOrderTwoKernelAxis

variable {G Q : Type*} [Group G] [Group Q] {pi : G →* Q}

/-- Complete the second central step using only the four-element bound on
the whole kernel. -/
noncomputable def toCentralSeries [Finite G]
    (A : CentralOrderTwoKernelAxis pi)
    (hkernel : Nat.card pi.ker ≤ 4) :
    BinaryNormalKernelCentralSeries G pi.ker :=
  binaryNormalKernelCentralSeries_of_central_order_two
    pi.ker A.C A.C_le_kernel A.C_card A.C_le_center hkernel

/-- Postcomposition by an injective homomorphism does not change the
selected kernel axis. -/
noncomputable def postcomp
    {Q' : Type*} [Group Q']
    (A : CentralOrderTwoKernelAxis pi)
    (j : Q →* Q') (_hj : Function.Injective j) :
    CentralOrderTwoKernelAxis (j.comp pi) where
  C := A.C
  normalC := inferInstance
  C_le_kernel := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    rw [MonoidHom.comp_apply, (MonoidHom.mem_ker.mp (A.C_le_kernel hx)), map_one]
  C_card := A.C_card
  C_le_center := A.C_le_center

/-- Transport a selected kernel axis through an isomorphism of source
groups. -/
noncomputable def mapDomainEquiv
    {G' : Type*} [Group G']
    (A : CentralOrderTwoKernelAxis pi)
    (e : G ≃* G') (pi' : G' →* Q)
    (hpi : pi'.comp e.toMonoidHom = pi) :
    CentralOrderTwoKernelAxis pi' := by
  let C' : Subgroup G' := A.C.map e.toMonoidHom
  have hCcenter : C' ≤ Subgroup.center G' := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := hz
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_center_iff.mp (A.C_le_center hc) x)
  have hCnormal : C'.Normal := by
    constructor
    intro z hz y
    have hzc := hCcenter hz
    simpa [Subgroup.mem_center_iff.mp hzc y, mul_assoc] using hz
  letI : C'.Normal := hCnormal
  refine
    { C := C'
      normalC := hCnormal
      C_le_kernel := ?_
      C_card := ?_
      C_le_center := hCcenter }
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := hz
    apply MonoidHom.mem_ker.mpr
    have h := congrArg (fun f : G →* Q => f c) hpi
    simpa only [MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp (A.C_le_kernel hc)] using h
  · exact (Nat.card_congr
      (A.C.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans
        A.C_card

end CentralOrderTwoKernelAxis

namespace SemidirectBinaryKernelCentralAxis

variable {N H N' H' : Type*}
  [Group N] [Group H] [Group N'] [Group H']
  [Finite H]
  {phi : H →* MulAut N} {psi : H' →* MulAut N'}

/-- A semidirect-product map is injective when both component maps are
injective. -/
theorem map_injective
    (fN : N →* N') (fH : H →* H')
    (hcompat : ∀ h : H,
      fN.comp (phi h).toMonoidHom =
        (psi (fH h)).toMonoidHom.comp fN)
    (hfN : Function.Injective fN)
    (hfH : Function.Injective fH) :
    Function.Injective (SemidirectProduct.map fN fH hcompat) := by
  intro x y hxy
  apply SemidirectProduct.ext
  · apply hfN
    exact congrArg SemidirectProduct.left hxy
  · apply hfH
    exact congrArg SemidirectProduct.right hxy

/-- The central order-two axis in a semidirect-product map whose normal
factor map is an isomorphism. -/
noncomputable def ofTopKernel
    (fN : N ≃* N') (fH : H →* H')
    (hcompat : ∀ h : H,
      fN.toMonoidHom.comp (phi h).toMonoidHom =
        (psi (fH h)).toMonoidHom.comp fN.toMonoidHom)
    (hH : IsPGroup 2 H)
    (hkernel_ne : fH.ker ≠ ⊥)
    (hkernel_card : Nat.card fH.ker ≤ 4) :
    CentralOrderTwoKernelAxis
      (SemidirectProduct.map fN.toMonoidHom fH hcompat) := by
  let S : BinaryNormalKernelCentralSeries H fH.ker :=
    binaryNormalKernelCentralSeries_of_card_le_four
      hH fH.ker hkernel_ne hkernel_card
  let i : H →* N ⋊[phi] H := SemidirectProduct.inr
  let C : Subgroup (N ⋊[phi] H) := S.C.map i
  have haction : ∀ c : S.C, phi (c : H) = 1 := by
    intro c
    apply MulEquiv.ext
    intro n
    apply fN.injective
    have hc : fH (c : H) = 1 :=
      MonoidHom.mem_ker.mp (S.C_le_K c.property)
    have h := DFunLike.ext_iff.mp (hcompat (c : H)) n
    simpa only [MonoidHom.comp_apply, hc, map_one,
      MulAut.one_apply, MulEquiv.coe_toMonoidHom] using h
  have hCcenter : C ≤ Subgroup.center (N ⋊[phi] H) := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply SemidirectProduct.ext
    · simp only [SemidirectProduct.mul_left, i,
        SemidirectProduct.left_inr, SemidirectProduct.right_inr,
        one_mul, map_one, MulAut.one_apply, mul_one]
      exact (congrArg (fun a : MulAut N => a x.left)
        (haction ⟨c, hc⟩)).symm
    · simpa only [SemidirectProduct.mul_right,
        SemidirectProduct.right_inr] using
          Subgroup.mem_center_iff.mp (S.C_le_center hc) x.right
  have hCnormal : C.Normal := by
    constructor
    intro z hz x
    have hzc := hCcenter hz
    simpa [Subgroup.mem_center_iff.mp hzc x, mul_assoc] using hz
  letI : C.Normal := hCnormal
  refine
    { C := C
      normalC := hCnormal
      C_le_kernel := ?_
      C_card := ?_
      C_le_center := hCcenter }
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := hz
    apply MonoidHom.mem_ker.mpr
    apply SemidirectProduct.ext
    · simp [i]
    · simpa only [SemidirectProduct.map_right,
        SemidirectProduct.right_inr] using
          MonoidHom.mem_ker.mp (S.C_le_K hc)
  · exact (Nat.card_congr
      (S.C.equivMapOfInjective i SemidirectProduct.inr_injective).toEquiv).symm.trans
        S.C_card

end SemidirectBinaryKernelCentralAxis
end SymmetricSubgroupAsymptotics

end
