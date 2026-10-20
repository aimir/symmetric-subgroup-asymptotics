import SymmetricSubgroupAsymptotics.SixPairFullKernelNormalDichotomy
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-! Identify the literal coarse-center coordinates with the actual kernel
center, and turn the constructive coordinate partition into N<=Z or Z<=N
for the SAME original normal subgroup. Physical independence is explicit. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairFullKernelCenter
open SixPairCoarseCenterTransport
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalCommutators

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

private theorem diagonal_ne_one : diagonal≠(1 : Equiv.Perm Points) := by decide +kernel

private theorem coordinate_cases
    (x : (SixPairNestedTopFrames.nestedFrame F E).top.ker)
    (s : Fin 3 → ZMod 2) (hs : HasBits F E x s) (j : Fin 3) :
    (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j x=1 ∨
      (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j x=diagonal := by
  have hb : ∀ a : ZMod 2,a=0 ∨ a=1 := by decide +kernel
  rcases hb (s j) with h0 | h1
  · left
    apply Equiv.ext
    rintro ⟨a,b⟩
    rw [hs j a b]
    simp only [h0,add_zero,Equiv.Perm.one_apply]
  · right
    apply Equiv.ext
    rintro ⟨a,b⟩
    rw [hs j a b,h1]
    rfl

/-- Full physical independence characterizes the ACTUAL kernel center. -/
theorem hasBits_iff_center
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (x : (SixPairNestedTopFrames.nestedFrame F E).top.ker) :
    (∃ s,HasBits F E x s) ↔
      x∈Subgroup.center (SixPairNestedTopFrames.nestedFrame F E).top.ker := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  constructor
  · rintro ⟨s,hs⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply C.kernelCoordinates_joint_injective
    funext j
    change C.kernelCoordinate j (y*x)=C.kernelCoordinate j (x*y)
    rw [map_mul,map_mul]
    rcases coordinate_cases F E x s hs j with h1 | hd
    · rw [h1]
      simp only [mul_one,one_mul]
    · rw [hd]
      exact (diagonal_commutes (C.kernelCoordinate j y)
        (SixPairThreePairKernelClassTwo.coordinate_preserves F E j y)).symm
  · intro hx
    have hc : ∀ j,C.kernelCoordinate j x=1 ∨ C.kernelCoordinate j x=diagonal := by
      intro j
      by_contra hh
      push Not at hh
      obtain ⟨h1,hd⟩ := hh
      obtain ⟨b,hb,hcomm⟩ := noncentral_witness (C.kernelCoordinate j x)
        (SixPairThreePairKernelClassTwo.coordinate_preserves F E j x) h1 hd
      let v : Fin 3 → Equiv.Perm Points := fun i => if i=j then b else 1
      have hv : ∀ i,Preserves (v i) := by
        intro i
        by_cases hi : i=j
        · simpa only [v,if_pos hi] using hb
        · simp only [v,if_neg hi]
          intro a b hab
          exact hab
      obtain ⟨y,hy⟩ := hfull v hv
      have hyj : C.kernelCoordinate j y=b := by simpa only [v,if_pos rfl] using hy j
      have he := congrArg (C.kernelCoordinate j) ((Subgroup.mem_center_iff.mp hx y).symm)
      simp only [map_mul] at he
      rw [hyj] at he
      have hone : C.kernelCoordinate j x*b*(C.kernelCoordinate j x)⁻¹*b⁻¹=1 := by
        rw [he]
        group
      exact diagonal_ne_one (hcomm.symm.trans hone)
    let s : Fin 3 → ZMod 2 := fun j => if C.kernelCoordinate j x=diagonal then 1 else 0
    refine ⟨s,?_⟩
    intro j a b
    dsimp only [s]
    split_ifs with hd
    · exact congrArg (fun p : Equiv.Perm Points => p (a,b)) hd
    · have h1 := (hc j).resolve_right hd
      simpa only [Equiv.Perm.one_apply,add_zero] using
        congrArg (fun p : Equiv.Perm Points => p (a,b)) h1

/-- The actual center viewed as an original subgroup of U. -/
def centerImage : Subgroup U :=
  (Subgroup.center (SixPairNestedTopFrames.nestedFrame F E).top.ker).map
    (SixPairNestedTopFrames.nestedFrame F E).top.ker.subtype

instance centerImage_normal : (centerImage F E).Normal := by
  unfold centerImage
  infer_instance

theorem centerImage_le_kernel : centerImage F E≤(SixPairNestedTopFrames.nestedFrame F E).top.ker := by
  rintro u ⟨x,hx,rfl⟩
  exact x.property

theorem mem_centerImage (x : (SixPairNestedTopFrames.nestedFrame F E).top.ker) :
    x.val∈centerImage F E ↔ x∈Subgroup.center (SixPairNestedTopFrames.nestedFrame F E).top.ker := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    have he : y=x := Subtype.ext hxy
    exact he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- Every actual retained nonbinary normal axis can now use this standard
subgroup partition after the checked N<=original-kernel theorem. -/
theorem normal_dichotomy [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (N : Subgroup U) [N.Normal]
    (hN : N≤(SixPairNestedTopFrames.nestedFrame F E).top.ker) :
    N≤centerImage F E ∨ centerImage F E≤N := by
  rcases SixPairFullKernelNormalDichotomy.normal_dichotomy F E hfull N with h | h
  · left
    intro u hu
    let x : (SixPairNestedTopFrames.nestedFrame F E).top.ker := ⟨u,hN hu⟩
    exact (mem_centerImage F E x).mpr ((hasBits_iff_center F E hfull x).mp (h x hu))
  · right
    rintro u ⟨x,hx,rfl⟩
    exact h x ((hasBits_iff_center F E hfull x).mpr hx)

end SymmetricSubgroupAsymptotics.SixPairFullKernelCenter
