import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntrinsicImage
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformGramCoordinates

/-! Primitive INTEGER coordinates on the actual intrinsic parity lattice.
Unlike full ambient coordinates, these need no factor two. Rational Gram
faithfulness is used only to prove that these literal coordinates separate
integer matrices. No source realization is assumed injective. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicPrimitiveCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDIntrinsicIntegralLattice
variable (r : ℕ) (hr : 4 ≤ r)

def diagonalInto : lattice r→ₗ[ℤ]CFSGOrthogonalDCartanParityLattice.evenSum r :=
  ((diagonal r).comp (lattice r).subtype).codRestrict _ (fun M=>M.property.2)

def coordinates (hr : 4 ≤ r) : lattice r→ₗ[ℤ](BasisIndex r→ℤ) :=
  LinearMap.pi (fun
    | .inl i=>(LinearMap.proj i).comp
        ((CFSGOrthogonalDCartanIntrinsicEquiv.coordinates r hr).comp (diagonalInto r))
    | .inr j=>(LinearMap.proj j).comp
        ((CFSGOrthogonalDUniformRootCoordinates.coordinates ℤ r).comp (lattice r).subtype))

theorem cast_cartan (a : CFSGOrthogonalDCartanParityLattice.evenSum r) :
    CFSGOrthogonalDCartanIntrinsicCoordinates.rationalCoordinates r hr a.val=
      fun i=>(CFSGOrthogonalDCartanIntrinsicEquiv.coordinates r hr a i:ℚ) := by
  obtain ⟨b,rfl⟩:=(CFSGOrthogonalDCartanIntrinsicEquiv.equiv r hr).surjective a
  have hc : CFSGOrthogonalDCartanIntrinsicEquiv.coordinates r hr
      (CFSGOrthogonalDCartanIntrinsicEquiv.equiv r hr b)=b :=
    (CFSGOrthogonalDCartanIntrinsicEquiv.equiv r hr).symm_apply_apply b
  rw [hc]
  change CFSGOrthogonalDCartanIntrinsicCoordinates.rationalCoordinates r hr
    (Fintype.linearCombination ℤ (CFSGOrthogonalDCartanParityLattice.column r) b)=_
  exact CFSGOrthogonalDCartanIntrinsicEquiv.rationalCoordinates_combination r hr b

theorem cast_coordinates (M : lattice r) (j : BasisIndex r) :
    (coordinates r hr M j:ℚ)=CFSGOrthogonalDUniformRationalFamily.coordinates r hr
      ((Int.castRingHom ℚ).mapMatrix M.val) j := by
  cases j with
  | inl i =>
    have h:=congrFun (cast_cartan r hr (diagonalInto r M)) i
    change (CFSGOrthogonalDCartanIntrinsicEquiv.coordinates r hr (diagonalInto r M) i:ℚ)=
      CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
        (CFSGOrthogonalDUniformRationalFamily.diagonal r ((Int.castRingHom ℚ).mapMatrix M.val)) i
    have hd : CFSGOrthogonalDUniformRationalFamily.diagonal r
        ((Int.castRingHom ℚ).mapMatrix M.val)=fun k=>((diagonalInto r M).val k:ℚ) := rfl
    rw [hd,CFSGOrthogonalDRationalCartanCoordinates.coordinates_cast]
    exact h.symm
  | inr j => rfl

theorem cast_mem_orthogonal (M : lattice r) :
    CFSGOrthogonalDUniformGramCoordinates.Orthogonal r
      ((Int.castRingHom ℚ).mapMatrix M.val) := by
  have hM : M.val ∈ skewAdjointMatricesLieSubalgebra (gram ℤ r) := M.property.1
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule] at hM
  change M.val.transpose*gram ℤ r=gram ℤ r*(-M.val) at hM
  have h:=congrArg (Int.castRingHom ℚ).mapMatrix hM
  have ht (X : Mat ℤ r) : (Int.castRingHom ℚ).mapMatrix X.transpose=
      ((Int.castRingHom ℚ).mapMatrix X).transpose := rfl
  have hg : (Int.castRingHom ℚ).mapMatrix (gram ℤ r)=gram ℚ r := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [gram,RingHom.mapMatrix,Matrix.map_apply]
  rw [CFSGOrthogonalDUniformGramCoordinates.Orthogonal,
    mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  simpa only [map_mul,map_neg,ht,hg] using h

theorem coordinates_injective : Function.Injective (coordinates r hr) := by
  intro M N h
  apply Subtype.ext
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (Index r)
  apply CFSGOrthogonalDUniformGramCoordinates.coordinates_injective r hr _ _
    (cast_mem_orthogonal r M) (cast_mem_orthogonal r N)
  funext j
  rw [←cast_coordinates r hr M j,←cast_coordinates r hr N j]
  exact congrArg (fun z : ℤ=>(z:ℚ)) (congrFun h j)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicPrimitiveCoordinates
