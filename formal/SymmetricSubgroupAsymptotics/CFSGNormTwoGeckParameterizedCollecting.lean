import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalParameterizedCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticParameterizedCollectingTransport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup

/-! Actual adjacent collecting at arbitrary parameters in every
coefficient ring. No rational denominators are cancelled after reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticCollectingTransport CFSGSerreQuadraticParameterizedCollectingTransport
open CFSGNormTwoGeckPositivePGroup
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem adjacent_word (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j= -1) (t a : K) :
    canonicalRoot (realizationData A hs hp b s) K false i t*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹*
      (canonicalRoot (realizationData A hs hp b s) K false j a)⁻¹=
      canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j (a*t)*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹ := by
  exact CFSGSerreQuadraticParameterizedCollectingTransport.collecting_word_of_rational
    (realizationData A hs hp b s) K i j
    (fun t a=>CFSGNormTwoGeckRationalParameterizedCollecting.adjacent_word
      A hs hp b s i j hij t a) t a

theorem adjacent_conjugation_factor (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j= -1) (t a : K) :
    canonicalRoot (realizationData A hs hp b s) K false i t*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹=
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j (a*t)*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹*
      canonicalRoot (realizationData A hs hp b s) K false j a := by
  have hh := congrArg
    (fun z : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ=>
      z*canonicalRoot (realizationData A hs hp b s) K false j a)
    (adjacent_word A hs hp b s K i j hij t a)
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedCollecting
