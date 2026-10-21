import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixOperators

/-! The original D rational representation installs the shared integral,
divided-power and tensor-realization construction with proved fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
open CFSG.Models.Chevalley

def integerGenerator (r : ℕ) : CartanMatrix.Generators (Fin r)→Mat ℤ r
  | .H i => cartan ℤ r i
  | .E i => positive ℤ r i
  | .F i => negative ℤ r i

def realizationData (r : ℕ) (hr : 4≤r) :
    CFSGSerreSquareZeroMatrix.Data (CartanMatrix.D r) (Index r) where
  rational := rationalOrthogonalRepresentation r hr
  integerGenerator := integerGenerator r
  generator_cast := by
    intro g
    cases g with
    | H i => simpa only [integerGenerator,rationalOrthogonalRepresentation_H] using map_cartan ℤ r (Int.castRingHom ℚ) i
    | E i => simpa only [integerGenerator,rationalOrthogonalRepresentation_E] using map_positive ℤ r (Int.castRingHom ℚ) i
    | F i => simpa only [integerGenerator,rationalOrthogonalRepresentation_F] using map_negative ℤ r (Int.castRingHom ℚ) i
  root_square_zero := by
    intro neg i
    cases neg
    · exact positive_sq_zero ℤ r i
    · exact negative_sq_zero ℤ r i

theorem realizationData_fieldRoot (K : Type*) [CommRing K] (r : ℕ) (hr : 4≤r)
    (neg : Bool) (i : Fin r) :
    CFSGSerreSquareZeroMatrix.fieldRoot (realizationData r hr) K neg i=rootMatrix K r neg i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (positive ℤ r i)=positive K r i
    exact map_positive ℤ r (Int.castRingHom K) i
  · change (Int.castRingHom K).mapMatrix (negative ℤ r i)=negative K r i
    exact map_negative ℤ r (Int.castRingHom K) i

abbrev integralOrthogonalRepresentation (r : ℕ) (hr : 4≤r) :=
  CFSGSerreSquareZeroMatrix.integralRepresentation (realizationData r hr)

abbrev orthogonalBaseChange (K : Type*) [CommRing K] (r : ℕ) (hr : 4≤r) :=
  CFSGSerreSquareZeroMatrix.baseChange (realizationData r hr) K

theorem orthogonalBaseChange_E (K : Type*) [CommRing K] (r : ℕ) (hr : 4≤r) (i : Fin r) :
    orthogonalBaseChange K r hr (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (CartanMatrix.Generators.E i))=positive K r i := by
  rw [CFSGSerreSquareZeroMatrix.baseChange_generator]
  change (Int.castRingHom K).mapMatrix (positive ℤ r i)=positive K r i
  exact map_positive ℤ r (Int.castRingHom K) i

theorem orthogonalBaseChange_F (K : Type*) [CommRing K] (r : ℕ) (hr : 4≤r) (i : Fin r) :
    orthogonalBaseChange K r hr (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator (CartanMatrix.D r) (CartanMatrix.Generators.F i))=negative K r i := by
  rw [CFSGSerreSquareZeroMatrix.baseChange_generator]
  change (Int.castRingHom K).mapMatrix (negative ℤ r i)=negative K r i
  exact map_negative ℤ r (Int.castRingHom K) i

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
