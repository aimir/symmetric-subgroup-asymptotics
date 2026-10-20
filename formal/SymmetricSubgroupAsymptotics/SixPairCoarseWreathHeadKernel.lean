import SymmetricSubgroupAsymptotics.SixPairCoarseWreathHead
import Mathlib.Algebra.CharP.Two

/-! The original center is EXACTLY the kernel of the physical two-head
map. Consequently the actual original quotient U/Z injects into the two
copies of the three-coordinate binary permutation module over its retained
top. No quotient is declared to have a transitive action on twelve points. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SixPairCoarseWreathHeadKernel
open SixPairFullKernelCenter SixPairCoarseCenterTransport SixPairCoarseWreathHead
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalCommutators BinaryTwoLayerLocalHead

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

/-- Equality on the literal original subgroups, not only isomorphic kernels. -/
theorem ker_head
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    (headHom F E).ker=centerImage F E := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  ext u
  constructor
  · intro hu
    have he := MonoidHom.mem_ker.mp hu
    have ht := congrArg PermutationalWreathProduct.right he
    change C.top.rangeRestrict u=1 at ht
    have hku : C.top u=1 :=
      congrArg (fun t : C.top.range => (t : Equiv.Perm (Fin 3))) ht
    let x : C.top.ker := ⟨u,hku⟩
    have hc : ∀ j,C.kernelCoordinate j x=1 ∨ C.kernelCoordinate j x=diagonal := by
      intro j
      have hj := congrArg
        (fun w : PermutationalWreathProduct (Multiplicative Points) C.top.range (Fin 3) => w.left j) he
      change Multiplicative.ofAdd (head ((C.wreathEmbedding u).left j))=1 at hj
      have hh := congrArg Multiplicative.toAdd hj
      rw [local_of_kernel F E x j] at hh
      exact (head_zero_iff (C.kernelCoordinate j x)
        (SixPairThreePairKernelClassTwo.coordinate_preserves F E j x)).mp hh
    have hx : x∈Subgroup.center C.top.ker := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply C.kernelCoordinates_joint_injective
      funext j
      change C.kernelCoordinate j (y*x)=C.kernelCoordinate j (x*y)
      rw [map_mul,map_mul]
      rcases hc j with h1 | hd
      · rw [h1]
        simp only [mul_one,one_mul]
      · rw [hd]
        exact (diagonal_commutes (C.kernelCoordinate j y)
          (SixPairThreePairKernelClassTwo.coordinate_preserves F E j y)).symm
    exact (mem_centerImage F E x).mpr hx
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨s,hs⟩ := (hasBits_iff_center F E hfull x).mpr hx
    apply MonoidHom.mem_ker.mpr
    apply PermutationalWreathProduct.ext
    · funext j
      change Multiplicative.ofAdd (head ((C.wreathEmbedding x.val).left j))=1
      rw [local_of_kernel F E x j]
      have hh : head (C.kernelCoordinate j x)=0 := by
        change (((C.kernelCoordinate j x) (0,0)).1,
          ((C.kernelCoordinate j x) (0,0)).2+((C.kernelCoordinate j x) (1,0)).2)=(0,0)
        rw [hs j 0 0,hs j 1 0]
        simp only [zero_add,CharTwo.add_self_eq_zero]
      rw [hh]
      rfl
    · change C.top.rangeRestrict x.val=1
      exact Subtype.ext x.property

/-- The faithful head embedding of the ACTUAL original center quotient. -/
def quotientHead
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    (U ⧸ centerImage F E) →*
      PermutationalWreathProduct (Multiplicative Points)
        (SixPairNestedTopFrames.nestedFrame F E).top.range (Fin 3) :=
  QuotientGroup.lift (centerImage F E) (headHom F E) (ker_head F E hfull).symm.le

theorem quotientHead_injective
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) :
    Function.Injective (quotientHead F E hfull) := by
  rw [←MonoidHom.ker_eq_bot_iff]
  unfold quotientHead
  rw [QuotientGroup.ker_lift,ker_head F E hfull,QuotientGroup.map_mk'_self]

@[simp] theorem quotientHead_mk
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E) (u : U) :
    quotientHead F E hfull (QuotientGroup.mk' (centerImage F E) u)=headHom F E u := rfl

end SymmetricSubgroupAsymptotics.SixPairCoarseWreathHeadKernel
