import SymmetricSubgroupAsymptotics.SixPairThreePairKernelClassTwo
import SymmetricSubgroupAsymptotics.BinaryTwoLayerLocalCommutators

/-! An actual normal denominator detects a literal single-fibre center
coordinate when the physical coarse kernel has independent local factors.
Independence is an explicit structural surjectivity condition, not inferred
from a local image, group order, or census label. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SixPairIndependentKernelNormalCommutators
open BinaryTwoLayerLocalClassTwo BinaryTwoLayerLocalCommutators

variable {X I J : Type} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I) (E : ProductBlockFrame F.top.range J (ZMod 2))

/-- The exact physical independence assertion for the original kernel. -/
def Independent : Prop :=
  ∀ v : J → Equiv.Perm Points, (∀ j,Preserves (v j)) →
    ∃ u : (SixPairNestedTopFrames.nestedFrame F E).top.ker,
      ∀ j,(SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j u=v j

/-- A noncentral actual coordinate in N produces the entire nontrivial
center element on that single physical fibre, inside the SAME N. -/
theorem single_center_mem (hfull : Independent F E)
    (N : Subgroup U) [N.Normal]
    (x : (SixPairNestedTopFrames.nestedFrame F E).top.ker) (hx : x.val∈N)
    (j : J)
    (h1 : (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j x≠1)
    (hd : (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate j x≠diagonal) :
    ∃ z : (SixPairNestedTopFrames.nestedFrame F E).top.ker,
      z.val∈N ∧ ∀ i,
        (SixPairNestedTopFrames.nestedFrame F E).kernelCoordinate i z=
          if i=j then diagonal else 1 := by
  classical
  let C := SixPairNestedTopFrames.nestedFrame F E
  obtain ⟨b,hb,hcomm⟩ := noncentral_witness (C.kernelCoordinate j x)
    (SixPairThreePairKernelClassTwo.coordinate_preserves F E j x) h1 hd
  let v : J → Equiv.Perm Points := fun i => if i=j then b else 1
  have hv : ∀ i,Preserves (v i) := by
    intro i
    by_cases hi : i=j
    · simpa only [v,if_pos hi] using hb
    · simp only [v,if_neg hi]
      intro a b hab
      exact hab
  obtain ⟨y,hy⟩ := hfull v hv
  let z : C.top.ker := x*y*x⁻¹*y⁻¹
  refine ⟨z,?_,?_⟩
  · have hconj : y.val*x.val⁻¹*y.val⁻¹∈N :=
      Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hx) y.val
    have hz := N.mul_mem hx hconj
    change x.val*y.val*x.val⁻¹*y.val⁻¹∈N
    simpa only [mul_assoc] using hz
  · intro i
    change C.kernelCoordinate i (x*y*x⁻¹*y⁻¹)=_
    simp only [map_mul,map_inv]
    rw [hy i]
    by_cases hi : i=j
    · subst i
      simpa only [v,if_pos rfl] using hcomm
    · simp [v,hi]

end SymmetricSubgroupAsymptotics.SixPairIndependentKernelNormalCommutators
