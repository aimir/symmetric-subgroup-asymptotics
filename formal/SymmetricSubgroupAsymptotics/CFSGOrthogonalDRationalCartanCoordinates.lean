import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanIntrinsicEquiv

/-! Rational extension of the proved intrinsic integer Cartan coordinates.
This is a rational linear map, used only before reduction. The integral
coordinate inverse continues to have the intrinsic even-sum codomain. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDRationalCartanCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDCartanParityLattice
open CFSGOrthogonalDCartanParitySpan CFSGOrthogonalDCartanIntrinsicCoordinates
variable (r : ℕ) (hr : 4 ≤ r)

def coordinates : (Fin r→ℚ)→ₗ[ℚ](Fin r→ℚ) :=
  Fintype.linearCombination ℚ (fun i=>rationalCoordinates r hr (unit r i))

theorem coordinates_cast (a : Fin r→ℤ) :
    coordinates r hr (fun i=>(a i:ℚ))=rationalCoordinates r hr a := by
  have ha : (∑ i : Fin r,a i • unit r i)=a := by
    funext j
    simp [unit,Finset.sum_apply,Pi.single_apply]
  have hc:=congrArg (rationalCoordinates r hr) ha
  simp only [map_sum,map_smul] at hc
  change Fintype.linearCombination ℚ
    (fun i=>rationalCoordinates r hr (unit r i)) (fun i=>(a i:ℚ))=_
  rw [Fintype.linearCombination_apply]
  convert hc using 1

theorem coordinates_column (j : Fin r) :
    coordinates r hr (fun k=>(column r j k:ℚ))=Pi.single j 1 := by
  rw [coordinates_cast,rationalCoordinates_column]

theorem coordinates_cartan (j : Fin r) :
    coordinates r hr (fun k=>cartan ℚ r j (.inl k) (.inl k))=Pi.single j 1 := by
  have he : (fun k=>cartan ℚ r j (.inl k) (.inl k))=
      fun k=>(column r j k:ℚ) := by
    funext k
    have h:=congrArg (fun M : Mat ℚ r=>M (.inl k) (.inl k))
      (map_cartan ℤ r (Int.castRingHom ℚ) j)
    exact h.symm
  rw [he,coordinates_column]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDRationalCartanCoordinates
