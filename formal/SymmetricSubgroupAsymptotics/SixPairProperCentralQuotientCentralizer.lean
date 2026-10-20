import SymmetricSubgroupAsymptotics.SixPairCentralIndicatorClosure

/-! For a proper original central denominator, centralization modulo that
SAME denominator already forces membership in the original kernel center.
Independent physical commutator witnesses rule out accidental extra
central elements in the quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientCentralizer
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalCommutators
open SixPairFullKernelCenter SixPairCentralIndicatorClosure

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)
  (E : ProductBlockFrame F.top.range (Fin 3) (ZMod 2))

/-- Actual commutators, rather than an assumed quotient type, detect the
center after every proper original central quotient. -/
theorem central_of_commutators_mem [MulAction.IsPretransitive U X]
    (hfull : SixPairIndependentKernelNormalCommutators.Independent F E)
    (N : Subgroup U) [N.Normal] (hproper : ¬centerImage F E≤N)
    (x : (SixPairNestedTopFrames.nestedFrame F E).top.ker)
    (hcomm : ∀ y : (SixPairNestedTopFrames.nestedFrame F E).top.ker,
      (x*y*x⁻¹*y⁻¹).val∈N) :
    x∈Subgroup.center (SixPairNestedTopFrames.nestedFrame F E).top.ker := by
  let C := SixPairNestedTopFrames.nestedFrame F E
  have hc : ∀ j,C.kernelCoordinate j x=1 ∨ C.kernelCoordinate j x=diagonal := by
    intro j
    by_contra hh
    push Not at hh
    obtain ⟨h1,hd⟩ := hh
    obtain ⟨b,hb,hlocal⟩ := noncentral_witness (C.kernelCoordinate j x)
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
    let z : C.top.ker := x*y*x⁻¹*y⁻¹
    have hz : z.val∈N := hcomm y
    have hcoords : ∀ i,C.kernelCoordinate i z=if i=j then diagonal else 1 := by
      intro i
      change C.kernelCoordinate i (x*y*x⁻¹*y⁻¹)=_
      simp only [map_mul,map_inv]
      rw [hy i]
      by_cases hi : i=j
      · subst i
        simpa only [v,if_pos rfl] using hlocal
      · simp [v,hi]
    exact hproper (center_le_of_indicator F E hfull N z hz j hcoords)
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

end SymmetricSubgroupAsymptotics.SixPairProperCentralQuotientCentralizer
