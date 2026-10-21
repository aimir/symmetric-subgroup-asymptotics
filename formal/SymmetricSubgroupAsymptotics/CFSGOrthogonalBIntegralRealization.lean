import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! Installs the original rational B representation in the shared integral
quadratic-root realization; every polynomial datum is proved in Z matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley

def integerGenerator (r : ℕ) : CartanMatrix.Generators (Fin r)→Mat ℤ r
  | .H i=>cartan ℤ r i
  | .E i=>positive ℤ r i
  | .F i=>negative ℤ r i

def realizationData (r : ℕ) :
    CFSGSerreQuadraticMatrix.Data (CartanMatrix.B r).transpose (Index r) where
  rational := rationalOrthogonalRepresentation r
  integerGenerator := integerGenerator r
  integerSecond := rootSecond ℤ r
  generator_cast := by
    intro g
    cases g with
    | H i=>simpa only [integerGenerator,rationalOrthogonalRepresentation_H] using map_cartan ℤ r (Int.castRingHom ℚ) i
    | E i=>simpa only [integerGenerator,rationalOrthogonalRepresentation_E] using map_positive ℤ r (Int.castRingHom ℚ) i
    | F i=>simpa only [integerGenerator,rationalOrthogonalRepresentation_F] using map_negative ℤ r (Int.castRingHom ℚ) i
  root_square := by
    intro neg i
    cases neg
    · exact positive_square ℤ r i
    · exact negative_square ℤ r i
  root_mul_second := by
    intro neg i
    cases neg
    · exact positive_mul_second ℤ r i
    · exact negative_mul_second ℤ r i
  second_mul_root := by
    intro neg i
    cases neg
    · exact second_mul_positive ℤ r i
    · exact second_mul_negative ℤ r i
  second_square := by
    intro neg i
    cases neg
    · exact positiveSecond_sq_zero ℤ r i
    · exact negativeSecond_sq_zero ℤ r i

theorem realizationData_fieldRoot (K : Type*) [CommRing K] (r : ℕ) (neg : Bool) (i : Fin r) :
    CFSGSerreQuadraticMatrix.fieldRoot (realizationData r) K neg i=rootMatrix K r neg i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (positive ℤ r i)=positive K r i
    exact map_positive ℤ r (Int.castRingHom K) i
  · change (Int.castRingHom K).mapMatrix (negative ℤ r i)=negative K r i
    exact map_negative ℤ r (Int.castRingHom K) i

theorem realizationData_fieldSecond (K : Type*) [CommRing K] (r : ℕ) (neg : Bool) (i : Fin r) :
    CFSGSerreQuadraticMatrix.fieldSecond (realizationData r) K neg i=rootSecond K r neg i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (positiveSecond ℤ r i)=positiveSecond K r i
    exact map_positiveSecond ℤ r (Int.castRingHom K) i
  · change (Int.castRingHom K).mapMatrix (negativeSecond ℤ r i)=negativeSecond K r i
    exact map_negativeSecond ℤ r (Int.castRingHom K) i

abbrev integralOrthogonalRepresentation (r : ℕ) :=
  CFSGSerreQuadraticMatrix.integralRepresentation (realizationData r)
abbrev orthogonalBaseChange (K : Type*) [CommRing K] (r : ℕ) :=
  CFSGSerreQuadraticMatrix.baseChange (realizationData r) K

theorem orthogonalBaseChange_E (K : Type*) [CommRing K] (r : ℕ) (i : Fin r) :
    orthogonalBaseChange K r (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator (CartanMatrix.B r).transpose (CartanMatrix.Generators.E i))=positive K r i := by
  rw [CFSGSerreQuadraticMatrix.baseChange_generator]
  exact map_positive ℤ r (Int.castRingHom K) i

theorem orthogonalBaseChange_F (K : Type*) [CommRing K] (r : ℕ) (i : Fin r) :
    orthogonalBaseChange K r (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator (CartanMatrix.B r).transpose (CartanMatrix.Generators.F i))=negative K r i := by
  rw [CFSGSerreQuadraticMatrix.baseChange_generator]
  exact map_negative ℤ r (Int.castRingHom K) i

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
