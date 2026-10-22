import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingTransport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings

/-! Orthogonal actual simple positive root units commute at arbitrary
parameters over every commutative coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCommutingRoots
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticParameterizedCollectingTransport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem orthogonal_word (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j=0) (t a : K) :
    parameterPositiveWord (realizationData A hs hp b s) K i j t a=1 := by
  exact CFSGSerreQuadraticCommutingTransport.commuting_word_of_rational
    (realizationData A hs hp b s) K i j
    (CFSGSerreQuadraticCommutingTransport.rational_commuting_word
      (realizationData A hs hp b s) i j
      (CFSGNormTwoGeckRationalAdjointStrings.lie_of_cartan_zero A hs hp b s i j hij)) t a

theorem orthogonal_conjugation (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j=0) (t a : K) :
    canonicalRoot (realizationData A hs hp b s) K false i t*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K false j a := by
  have hh := congrArg
    (fun z : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ=>
      z*canonicalRoot (realizationData A hs hp b s) K false j a)
    (orthogonal_word A hs hp b s K i j hij t a)
  simpa only [parameterPositiveWord,mul_assoc,inv_mul_cancel,mul_one,one_mul] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCommutingRoots
