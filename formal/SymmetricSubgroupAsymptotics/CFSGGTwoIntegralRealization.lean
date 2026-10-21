import SymmetricSubgroupAsymptotics.CFSGGTwoSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! The actual G₂ rational representation preserves the least original
integral lattice through the shared quadratic divided-power construction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
open CFSG.Models.Chevalley

 def rootMatrix (R : Type*) [CommRing R] (negativeRoot : Bool) (i : Fin 2) : Mat R :=
  if negativeRoot then negative R i else positive R i
 def rootSecond (R : Type*) [CommRing R] (negativeRoot : Bool) (i : Fin 2) : Mat R :=
  if negativeRoot then negativeSecond R i else positiveSecond R i

 theorem map_positiveSecond (R : Type*) [CommRing R] {S : Type*} [CommRing S]
    (f : R→+*S) (i : Fin 2) :
    f.mapMatrix (positiveSecond R i)=positiveSecond S i := by
  by_cases h : i=0
  · simp only [positiveSecond,if_pos h]
    change (Matrix.single _ _ (-1:R)).map f=Matrix.single _ _ (-1:S)
    simp only [Matrix.map_single,map_neg,map_one]
  · simp only [positiveSecond,if_neg h,map_zero]

 theorem map_negativeSecond (R : Type*) [CommRing R] {S : Type*} [CommRing S]
    (f : R→+*S) (i : Fin 2) :
    f.mapMatrix (negativeSecond R i)=negativeSecond S i := by
  change (positiveSecond R i).transpose.map f=(positiveSecond S i).transpose
  rw [Matrix.transpose_map]
  exact congrArg Matrix.transpose (map_positiveSecond R f i)

 def integerGenerator : CartanMatrix.Generators (Fin 2)→Mat ℤ
  | .H i=>cartan ℤ i
  | .E i=>positive ℤ i
  | .F i=>negative ℤ i

 def realizationData : CFSGSerreQuadraticMatrix.Data CartanMatrix.G₂ Index where
  rational := rationalRepresentation
  integerGenerator := integerGenerator
  integerSecond := rootSecond ℤ
  generator_cast := by
    intro g
    cases g with
    | H i=>simpa only [integerGenerator,rationalRepresentation_H] using map_cartan ℤ (Int.castRingHom ℚ) i
    | E i=>simpa only [integerGenerator,rationalRepresentation_E] using map_positive ℤ (Int.castRingHom ℚ) i
    | F i=>simpa only [integerGenerator,rationalRepresentation_F] using map_negative ℤ (Int.castRingHom ℚ) i
  root_square := by
    intro neg i
    cases neg
    · exact positive_square ℤ i
    · exact negative_square ℤ i
  root_mul_second := by
    intro neg i
    cases neg
    · exact positive_mul_second ℤ i
    · exact negative_mul_second ℤ i
  second_mul_root := by
    intro neg i
    cases neg
    · exact second_mul_positive ℤ i
    · exact second_mul_negative ℤ i
  second_square := by
    intro neg i
    cases neg
    · exact positiveSecond_sq_zero ℤ i
    · exact negativeSecond_sq_zero ℤ i

 theorem realizationData_fieldRoot (K : Type*) [CommRing K] (neg : Bool) (i : Fin 2) :
    CFSGSerreQuadraticMatrix.fieldRoot realizationData K neg i=rootMatrix K neg i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (positive ℤ i)=positive K i
    exact map_positive ℤ (Int.castRingHom K) i
  · change (Int.castRingHom K).mapMatrix (negative ℤ i)=negative K i
    exact map_negative ℤ (Int.castRingHom K) i

 theorem realizationData_fieldSecond (K : Type*) [CommRing K] (neg : Bool) (i : Fin 2) :
    CFSGSerreQuadraticMatrix.fieldSecond realizationData K neg i=rootSecond K neg i := by
  cases neg
  · change (Int.castRingHom K).mapMatrix (positiveSecond ℤ i)=positiveSecond K i
    exact map_positiveSecond ℤ (Int.castRingHom K) i
  · change (Int.castRingHom K).mapMatrix (negativeSecond ℤ i)=negativeSecond K i
    exact map_negativeSecond ℤ (Int.castRingHom K) i

 abbrev foldedBaseChange (K : Type*) [CommRing K] :=
  CFSGSerreQuadraticMatrix.baseChange realizationData K

 theorem foldedBaseChange_E (K : Type*) [CommRing K] (i : Fin 2) :
    foldedBaseChange K (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (CartanMatrix.Generators.E i))=positive K i := by
  rw [CFSGSerreQuadraticMatrix.baseChange_generator]
  exact map_positive ℤ (Int.castRingHom K) i

 theorem foldedBaseChange_F (K : Type*) [CommRing K] (i : Fin 2) :
    foldedBaseChange K (1 ⊗ₜ[ℤ]
      CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (CartanMatrix.Generators.F i))=negative K i := by
  rw [CFSGSerreQuadraticMatrix.baseChange_generator]
  exact map_negative ℤ (Int.castRingHom K) i

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
