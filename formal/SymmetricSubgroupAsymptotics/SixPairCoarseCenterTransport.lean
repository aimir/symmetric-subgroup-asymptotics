import SymmetricSubgroupAsymptotics.SixPairIndependentKernelNormalCommutators
import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance

/-! Literal coarse-center bit coordinates in the original pair kernel.
Original conjugation transports these coordinates by the ACTUAL coarse
top, and all original offsets cancel. No split model is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairCoarseCenterTransport

variable {X I J : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (E : ProductBlockFrame F.top.range J (ZMod 2))

private theorem coordinate_action
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (j : J)
    (p : ZMod 2 × ZMod 2) :
    (u.val : Equiv.Perm X) ((SixPairNestedTopFrames.nestedFrame F E).frame (j,p)) =
      (SixPairNestedTopFrames.nestedFrame F E).frame
        (j,(SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j u p) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  apply C.frame.symm.injective
  rw [C.frame.symm_apply_apply]
  apply Prod.ext
  · have h := C.intertwine u.val (j,p)
    rw [u.property] at h
    exact h
  · rfl

/-- A coarse bit toggles BOTH original pairs in the same four-point fibre. -/
def HasBits (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker)
    (s : J → ZMod 2) : Prop :=
  ∀ j a b,(SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j u (a,b)=
    (a,b+s j)

private theorem action_of_bits
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (s : J → ZMod 2)
    (hs : HasBits F E u s) (j : J) (a b : ZMod 2) :
    (u.val : Equiv.Perm X) (F.frame (E.frame (j,a),b))=
      F.frame (E.frame (j,a),b+s j) := by
  change (u.val : Equiv.Perm X)
      ((SixPairNestedTopFrames.nestedFrame F E).frame (j,(a,b))) =
    (SixPairNestedTopFrames.nestedFrame F E).frame (j,(a,b+s j))
  rw [coordinate_action F E,hs j a b]

/-- Coarse-center coordinates lie in the SAME original pair kernel. -/
theorem original_kernel
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (s : J → ZMod 2)
    (hs : HasBits F E u s) : u.val∈F.top.ker := by
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro i
  obtain ⟨⟨j,a⟩,rfl⟩ := E.frame.surjective i
  have h := F.intertwine u.val (E.frame (j,a),0)
  rw [action_of_bits F E u s hs j a 0,F.frame.symm_apply_apply] at h
  exact h.symm

def pairKernelLift
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (s : J → ZMod 2)
    (hs : HasBits F E u s) : F.top.ker :=
  ⟨u.val,original_kernel F E u s hs⟩

theorem pairKernelLift_bits
    (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (s : J → ZMod 2)
    (hs : HasBits F E u s) (j : J) (a : ZMod 2) :
    F.bits (pairKernelLift F E u s hs) (E.frame (j,a))=s j := by
  change (F.frame.symm ((u.val : Equiv.Perm X) (F.frame (E.frame (j,a),0)))).2=s j
  rw [action_of_bits F E u s hs j a 0,F.frame.symm_apply_apply,zero_add]

/-- Exact actual conjugation, with the inverse coarse permutation on bits. -/
theorem hasBits_conjugate
    (g : U) (u : (SixPairNestedTopFrames.nestedFrame F E).top.ker)
    (s : J → ZMod 2) (hs : HasBits F E u s) :
    HasBits F E (MulAut.conjNormal g u)
      (fun j => s (((SixPairNestedTopFrames.nestedFrame F E).top g)⁻¹ j)) := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  let k := pairKernelLift F E u s hs
  let l := MulAut.conjNormal g k
  have hkbits (i : I) : F.bits k i=s (E.frame.symm i).1 := by
    obtain ⟨⟨j,a⟩,rfl⟩ := E.frame.surjective i
    simpa only [E.frame.symm_apply_apply] using pairKernelLift_bits F E u s hs j a
  intro j a b
  have hbits := F.bits_conjNormal g k (E.frame (j,a))
  rw [hkbits] at hbits
  have hi := E.intertwine (F.top.rangeRestrict (g⁻¹)) (j,a)
  simp only [map_inv] at hi
  change (E.frame.symm ((F.top g)⁻¹ (E.frame (j,a)))).1=(C.top g)⁻¹ j at hi
  rw [hi] at hbits
  have hp := F.kernel_action_frame l (E.frame (j,a)) b
  rw [hbits] at hp
  have hpc : ((MulAut.conjNormal g u).val : Equiv.Perm X) (C.frame (j,(a,b)))=
      C.frame (j,(a,b+s ((C.top g)⁻¹ j))) := hp
  change (C.frame.symm
    (((MulAut.conjNormal g u).val : Equiv.Perm X) (C.frame (j,(a,b))))).2=_
  rw [hpc,C.frame.symm_apply_apply]

end SymmetricSubgroupAsymptotics.SixPairCoarseCenterTransport
