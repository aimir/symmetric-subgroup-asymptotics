import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntrinsicPrimitiveCoordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalScaledRealization
import SymmetricSubgroupAsymptotics.FiniteIntegralRationalFamilyScaledRetraction

/-! Actual original D source equals the intrinsic integer parity lattice.
The rational source spanning theorem and genuine integer intrinsic
coordinates reconstruct EVERY original integral vector, with scale ONE.
Thus the primitive source family Z-spans and survives all scalar extensions.
No integral-span, source-faithfulness or target-containment premise remains. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntrinsicEquivalence
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDIntrinsicIntegralLattice
open CFSGOrthogonalDOriginalIntrinsicImage
variable (r : ℕ) (hr : 4 ≤ r)
local instance : DecidableEq (BasisIndex r):=Classical.decEq _

def rationalCoordinates : RationalLie (CartanMatrix.D r)→ₗ[ℚ](BasisIndex r→ℚ) :=
  (CFSGOrthogonalDUniformRationalFamily.coordinates r hr).comp
    (rationalOrthogonalRepresentation r hr).toLinearMap

theorem rational_coordinates_vector (j : BasisIndex r) :
    rationalCoordinates r hr (vector r hr j).val=Pi.single j 1 := by
  change CFSGOrthogonalDUniformRationalFamily.coordinates r hr
    (rationalOrthogonalRepresentation r hr (vector r hr j).val)=_
  rw [CFSGOrthogonalDOriginalScaledRealization.rational_vector_image,
    CFSGOrthogonalDUniformRationalFamily.coordinates_matrix]

theorem rational_coordinates_cast (x : Source r) :
    rationalCoordinates r hr x.val=fun j=>
      (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr (realization r hr x) j:ℚ) := by
  funext j
  have h:=CFSGOrthogonalDIntrinsicPrimitiveCoordinates.cast_coordinates r hr
    (realization r hr x) j
  change (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr (realization r hr x) j:ℚ)=
    CFSGOrthogonalDUniformRationalFamily.coordinates r hr
      ((Int.castRingHom ℚ).mapMatrix (integralOrthogonalRepresentation r hr x)) j at h
  have hcast:=CFSGSerreSquareZeroMatrix.integralRepresentation_cast (realizationData r hr) x
  change (Int.castRingHom ℚ).mapMatrix (integralOrthogonalRepresentation r hr x)=
    rationalOrthogonalRepresentation r hr x.val at hcast
  rw [hcast] at h
  exact h.symm

theorem primitive_coordinates (j : BasisIndex r) :
    CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr
      (realization r hr (vector r hr j))=Pi.single j 1 := by
  funext k
  apply (Int.cast_injective : Function.Injective (fun z : ℤ=>(z:ℚ)))
  have h:=congrFun (rational_coordinates_cast r hr (vector r hr j)) k
  rw [rational_coordinates_vector] at h
  simpa [Pi.single_apply] using h.symm

theorem reconstruction (x : Source r) :
    Fintype.linearCombination ℤ (vector r hr)
      (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr (realization r hr x))=x := by
  have h:=FiniteIntegralRationalFamilyScaledRetraction.reconstruction_of_rational_mem
    (integralLattice (CartanMatrix.D r)) (realization r hr) (vector r hr)
    (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr)
    (rationalCoordinates r hr) 1 (by simpa only [Int.cast_one,one_smul] using rational_coordinates_vector r hr)
    (rational_coordinates_cast r hr) x (by
      change x.val ∈ Submodule.span ℚ
        (Set.range (CFSGOrthogonalDOriginalRationalFirstActionSpan.family r hr))
      rw [CFSGOrthogonalDOriginalRationalFirstActionSpan.span_eq_top r hr]
      trivial)
  simpa only [one_smul] using h

theorem span_eq_top : Submodule.span ℤ (Set.range (vector r hr))=⊤ := by
  apply top_unique
  intro x hx
  rw [←reconstruction r hr x,Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

theorem realization_injective : Function.Injective (realization r hr) := by
  intro x y h
  rw [←reconstruction r hr x,←reconstruction r hr y,h]

theorem realization_surjective : Function.Surjective (realization r hr) := by
  intro M
  refine ⟨Fintype.linearCombination ℤ (vector r hr)
    (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr M),?_⟩
  apply CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates_injective r hr
  exact FiniteIntegralFamilySplitRealization.coordinates_combination (realization r hr)
    (vector r hr) (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr)
    (primitive_coordinates r hr) _

def equiv : Source r≃ₗ[ℤ]lattice r :=
  LinearEquiv.ofBijective (realization r hr)
    ⟨realization_injective r hr,realization_surjective r hr⟩

theorem baseChange_injective (K : Type*) [CommRing K] :
    Function.Injective ((realization r hr).baseChange K) :=
  FiniteIntegralFamilySplitRealization.baseChange_injective (realization r hr)
    (vector r hr) (CFSGOrthogonalDIntrinsicPrimitiveCoordinates.coordinates r hr)
    (span_eq_top r hr) (primitive_coordinates r hr) K

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalIntrinsicEquivalence
