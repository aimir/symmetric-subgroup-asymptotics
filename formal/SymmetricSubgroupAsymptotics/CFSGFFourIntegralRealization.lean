import SymmetricSubgroupAsymptotics.CFSGFFourIntegralMatrices
import SymmetricSubgroupAsymptotics.CFSGFFourSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! Integral quadratic data for the ORIGINAL F4 Serre source. All four
polynomial identities are checked on the actual folded matrices before
invoking the shared divided-power/lattice descent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
local instance fFourIntegralRealizationDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

def integerGenerator : CartanMatrix.Generators (Fin 4)→IntMat
  | .H i=>integerH i
  | .E i=>integerE i
  | .F i=>integerF i

def integerSecond (neg : Bool) (i : Fin 4) : IntMat :=
  if neg then negativeSecondZ i else positiveSecondZ i

def integerRoot (neg : Bool) (i : Fin 4) : IntMat :=
  integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)

private theorem rational_quadratic (neg : Bool) (i : Fin 4) :
    (Int.castRingHom ℚ).mapMatrix (integerRoot neg i)*
        (Int.castRingHom ℚ).mapMatrix (integerRoot neg i)=
      (Int.castRingHom ℚ).mapMatrix (integerSecond neg i)+
        (Int.castRingHom ℚ).mapMatrix (integerSecond neg i) ∧
    (Int.castRingHom ℚ).mapMatrix (integerRoot neg i)*
        (Int.castRingHom ℚ).mapMatrix (integerSecond neg i)=0 ∧
    (Int.castRingHom ℚ).mapMatrix (integerSecond neg i)*
        (Int.castRingHom ℚ).mapMatrix (integerRoot neg i)=0 ∧
    (Int.castRingHom ℚ).mapMatrix (integerSecond neg i)*
        (Int.castRingHom ℚ).mapMatrix (integerSecond neg i)=0 := by
  cases neg
  · simpa only [integerRoot,integerGenerator,CFSGSerreSquareZeroMatrix.rootGenerator,
      integerSecond,Bool.false_eq_true,if_false,map_integerE,map_positiveSecondZ] using positive_quadratic i
  · simpa only [integerRoot,integerGenerator,CFSGSerreSquareZeroMatrix.rootGenerator,
      integerSecond,if_true,map_integerF,map_negativeSecondZ] using negative_quadratic i

private theorem integral_quadratic (neg : Bool) (i : Fin 4) :
    integerRoot neg i*integerRoot neg i=integerSecond neg i+integerSecond neg i ∧
      integerRoot neg i*integerSecond neg i=0 ∧ integerSecond neg i*integerRoot neg i=0 ∧
      integerSecond neg i*integerSecond neg i=0 := by
  obtain ⟨hs,hl,hr,hd⟩ := rational_quadratic neg i
  refine ⟨?_,?_,?_,?_⟩
  · apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
    change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix (_+_)
    simpa only [map_mul,map_add] using hs
  · apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
    change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
    simpa only [map_mul,map_zero] using hl
  · apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
    change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
    simpa only [map_mul,map_zero] using hr
  · apply CFSGSerreSquareZeroMatrix.integerCast_injective Index
    change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
    simpa only [map_mul,map_zero] using hd

def realizationData : CFSGSerreQuadraticMatrix.Data CartanMatrix.F₄ Index where
  rational := rationalRepresentation
  integerGenerator := integerGenerator
  integerSecond := integerSecond
  generator_cast := by
    intro g
    cases g with
    | H i=>simpa only [integerGenerator,rationalRepresentation_H] using map_integerH i
    | E i=>simpa only [integerGenerator,rationalRepresentation_E] using map_integerE i
    | F i=>simpa only [integerGenerator,rationalRepresentation_F] using map_integerF i
  root_square neg i := (integral_quadratic neg i).1
  root_mul_second neg i := (integral_quadratic neg i).2.1
  second_mul_root neg i := (integral_quadratic neg i).2.2.1
  second_square neg i := (integral_quadratic neg i).2.2.2

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
