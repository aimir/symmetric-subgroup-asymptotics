import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddTopKernel

/-! A cubic local stabilizer transports through the actual transitive
block image, so one such local cubic is enough for zero-odd top faithfulness. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneLocalCubicTransport
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingCentralizerCommutators (top)

theorem transport (C : Subgroup Frame) (i j : Fin 4) (h q : C)
    (hh : (h : Frame).right i=j) (hq : (q : Frame).right i=i)
    (hqc : (q : Frame).left i^3=1) (hqn : (q : Frame).left i≠1) :
    ∃ q' : C, (q' : Frame).right j=j ∧
      (q' : Frame).left j^3=1 ∧ (q' : Frame).left j≠1 := by
  let q' := h*q*h⁻¹
  have hin : (h : Frame).right⁻¹ j=i := by
    have he := congrArg (h : Frame).right.symm hh
    simpa only [Equiv.symm_apply_apply] using he.symm
  have ht : (q' : Frame).right j=j := by
    change (((h : Frame)*(q : Frame)*(h : Frame)⁻¹).right) j=j
    simp only [PermutationalWreathProduct.mul_right,PermutationalWreathProduct.inv_right,
      Equiv.Perm.mul_apply,hin,hq,hh]
  have hqi : (q' : Frame).right⁻¹ j=j := by
    have he := congrArg (q' : Frame).right.symm ht
    simpa only [Equiv.symm_apply_apply] using he.symm
  have hm : h*q=q'*h := by
    dsimp only [q']
    rw [mul_assoc,mul_assoc,inv_mul_cancel,mul_one]
  have he := congrArg (fun z : C => (z : Frame).left j) hm
  simp only [Subgroup.coe_mul,PermutationalWreathProduct.mul_left,Pi.mul_apply] at he
  change (h : Frame).left j*(q : Frame).left ((h : Frame).right⁻¹ j)=
    (q' : Frame).left j*(h : Frame).left ((q' : Frame).right⁻¹ j) at he
  rw [hin,hqi] at he
  have hl : (q' : Frame).left j=
      (h : Frame).left j*(q : Frame).left i*((h : Frame).left j)⁻¹ :=
    eq_mul_inv_iff_mul_eq.mpr he.symm
  let a := MulAut.conj ((h : Frame).left j)
  have hla : (q' : Frame).left j=a ((q : Frame).left i) := hl
  refine ⟨q',ht,?_,?_⟩
  · rw [hla,← map_pow,hqc,map_one]
  · intro hz
    apply hqn
    apply a.injective
    rw [map_one,← hla,hz]

theorem every_local (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (i : Fin 4) (q : C) (hq : (q : Frame).right i=i)
    (hqc : (q : Frame).left i^3=1) (hqn : (q : Frame).left i≠1) :
    ∀ j : Fin 4, ∃ q' : C, (q' : Frame).right j=j ∧
      (q' : Frame).left j^3=1 ∧ (q' : Frame).left j≠1 := by
  intro j
  obtain ⟨h,hh⟩ := BinaryPlaneAlternatingKernelPartition.transitive C heven i j
  exact transport C i j h q hh hq hqc hqn

/-- This implication proves top faithfulness instead of assuming it. -/
theorem top_injective (C : Subgroup Frame) (hzero : oddKernel C=⊥)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (i : Fin 4) (q : C) (hq : (q : Frame).right i=i)
    (hqc : (q : Frame).left i^3=1) (hqn : (q : Frame).left i≠1) :
    Function.Injective (top C) :=
  BinaryPlaneZeroOddTopKernel.top_injective C hzero
    (every_local C heven i q hq hqc hqn)

end SymmetricSubgroupAsymptotics.BinaryPlaneLocalCubicTransport
