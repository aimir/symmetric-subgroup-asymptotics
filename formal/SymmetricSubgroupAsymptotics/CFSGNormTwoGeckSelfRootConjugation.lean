import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSelfWeylString
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRationalRootValues
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationPolynomial
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCollectingTransport

/-! The original norm-two self-root Weyl identity. Its actual sl₂
brackets are proved first over the rationals; integer parameter-word
transport then gives the literal unit identity in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckRationalWeylCollecting
open CFSGSerreQuadraticCollectingTransport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem rational_self_root (i : Fin r) :
    (canonicalWeyl (realizationData A hs hp b s) ℚ i : Target b)*
      fieldRoot (realizationData A hs hp b s) ℚ false i*
      (((canonicalWeyl (realizationData A hs hp b s) ℚ i)⁻¹ : (Target b)ˣ) : Target b)=
        -fieldRoot (realizationData A hs hp b s) ℚ true i := by
  have hd := b.cartanMatrix_apply_same (s i)
  change cartan b s i i=2 at hd
  apply CFSGSerreQuadraticSelfWeylString.weyl_conjugates_self
    (realizationData A hs hp b s) i (H b s i)
  · rw [rational_E_eq,rational_F_eq,EF,if_pos rfl]
  · rw [rational_E_eq,HE,hd]
    module
  · rw [rational_F_eq,HF,hd]
    module

theorem rational_self_word (i : Fin r) (a : ℚ) :
    conjugateWord (realizationData A hs hp b s) ℚ i i a=
      canonicalRoot (realizationData A hs hp b s) ℚ true i (-a) := by
  apply Units.ext
  have hh := CFSGUnitConjugationPolynomial.conjugate_quadratic
    (canonicalWeyl (realizationData A hs hp b s) ℚ i)
    (fieldRoot (realizationData A hs hp b s) ℚ false i)
    (-fieldRoot (realizationData A hs hp b s) ℚ true i)
    (rational_self_root A hs hp b s i) a
  simpa only [conjugateWord,Units.val_mul,canonicalRoot_val_rational,
    neg_smul,smul_neg,neg_sq] using hh

theorem self_root_word (K : Type*) [CommRing K] (i : Fin r) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false i a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K true i (-a) := by
  let D := realizationData A hs hp b s
  let M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) (Polynomial ℤ) :=
    conjugateWord D (Polynomial ℤ) i i Polynomial.X
  let N : Matrix (b.support⊕Roots A) (b.support⊕Roots A) (Polynomial ℤ) :=
    canonicalRoot D (Polynomial ℤ) true i (-Polynomial.X)
  have hEval : ∀c : ℚ,(Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix M=
      (Polynomial.eval₂RingHom (Int.castRingHom ℚ) c).mapMatrix N := by
    intro c
    dsimp only [M,N]
    simpa only [map_conjugateWord_val,map_canonicalRoot_val,map_neg,
      Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using
      congrArg (fun u : (Target b)ˣ=>(u : Target b))
        (rational_self_word A hs hp b s i c)
  have hk := CFSGIntegerMatrixPolynomialTransport.evaluations_eq_of_rational_evaluations K M N hEval a
  apply Units.ext
  dsimp only [M,N] at hk
  simpa only [map_conjugateWord_val,conjugateWord,Units.val_mul,map_mul,
    map_canonicalWeyl_val,map_canonicalWeyl_inv_val,map_canonicalRoot_val,map_neg,
    Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X] using hk

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation
