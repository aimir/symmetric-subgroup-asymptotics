import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTruncation
import SymmetricSubgroupAsymptotics.CFSGGeckOppositionAlgEquiv

/-! The same quadratic identities for negative Geck roots, transported
through the actual integral-permutation opposition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegative
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckQuadratic
open CFSGNormTwoGeckTruncation CFSGGeckOppositionAlgEquiv
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def negativeSecondMatrix (i : b.support) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ :=
  opposition b (secondMatrix A hs hp b i)

theorem F_square (i : b.support) :
    (RootPairing.GeckConstruction.f i)^2=(2:ℚ) • negativeSecondMatrix A hs hp b i := by
  have hh := congrArg (opposition b) (E_square A hs hp b i)
  simpa only [map_pow,map_smul,opposition_E,negativeSecondMatrix] using hh

theorem F_mul_second (i : b.support) :
    RootPairing.GeckConstruction.f i*negativeSecondMatrix A hs hp b i=0 := by
  have hh := congrArg (opposition b) (E_mul_second A hs hp b i)
  simpa only [map_mul,map_zero,opposition_E,negativeSecondMatrix] using hh

theorem second_mul_F (i : b.support) :
    negativeSecondMatrix A hs hp b i*RootPairing.GeckConstruction.f i=0 := by
  have hh := congrArg (opposition b) (second_mul_E A hs hp b i)
  simpa only [map_mul,map_zero,opposition_E,negativeSecondMatrix] using hh

theorem F_cube (i : b.support) : (RootPairing.GeckConstruction.f i)^3=0 := by
  have hh := congrArg (opposition b) (E_cube A hs hp b i)
  simpa only [map_pow,map_zero,opposition_E] using hh

theorem negativeSecond_square (i : b.support) : (negativeSecondMatrix A hs hp b i)^2=0 := by
  have hh := congrArg (opposition b) (second_square A hs hp b i)
  simpa only [map_pow,map_zero,negativeSecondMatrix] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegative
