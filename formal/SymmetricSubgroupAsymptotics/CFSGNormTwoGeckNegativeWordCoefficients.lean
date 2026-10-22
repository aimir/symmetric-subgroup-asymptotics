import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeQuadraticGrade

/-! The two EXPLICIT coefficients of an actual negative-root Weyl word.
The first coefficient remains nonzero over every field because it is an
invertible conjugate of an original generator with a unit entry. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeWordCoefficients
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckNegativeQuadraticGrade
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWordLatticeSupport
open CFSGGradedMatrixSupport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s
local notation "ell" => latticeWeight A hs hp b

def firstCoefficient (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) :=
  CFSGAlgebraConjugationAction.action K
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (wordUnit A hs hp b s K w) (fieldRoot D K true i)

def secondCoefficient (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) :=
  CFSGAlgebraConjugationAction.action K
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
    (wordUnit A hs hp b s K w) (fieldSecond D K true i)

theorem word_expansion (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) (a : K) :
    ((wordUnit A hs hp b s K w*canonicalRoot D K true i a*
      (wordUnit A hs hp b s K w)⁻¹ : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)=
      1+a • firstCoefficient A hs hp b s K w i+a^2 • secondCoefficient A hs hp b s K w i := by
  simp only [Units.val_mul,canonicalRoot_val,firstCoefficient,secondCoefficient,
    CFSGAlgebraConjugationAction.action_apply,mul_add,add_mul,mul_one,
    mul_smul_comm,smul_mul_assoc,Units.mul_inv]

theorem first_support (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) :
    Supported ell (fun v=>v+wordLinear A hs hp b s w (-(s i:Roots A).val))
      (firstCoefficient A hs hp b s K w i) := by
  have hP := word_lattice_support A hs hp b s K w
  have hQ := word_lattice_support A hs hp b s K (inverseWord w)
  rw [wordUnit_inverseWord,wordLinear_inverseWord] at hQ
  exact supported_conjugation ell (wordLinear A hs hp b s w).toAddEquiv
    (-(s i:Roots A).val) _ _ _ hP
    (by simpa only [sub_eq_add_neg] using field_F_support A hs hp b s K i) hQ

theorem second_support (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) :
    Supported ell (fun v=>v+(wordLinear A hs hp b s w (-(s i:Roots A).val)+
      wordLinear A hs hp b s w (-(s i:Roots A).val)))
      (secondCoefficient A hs hp b s K w i) := by
  have hP := word_lattice_support A hs hp b s K w
  have hQ := word_lattice_support A hs hp b s K (inverseWord w)
  rw [wordUnit_inverseWord,wordLinear_inverseWord] at hQ
  have hh := supported_conjugation ell (wordLinear A hs hp b s w).toAddEquiv
    (-(s i:Roots A).val+ -(s i:Roots A).val) _ _ _ hP
    (field_negative_second_support A hs hp b s K i) hQ
  simpa only [map_add] using hh

theorem first_ne_zero (K : Type) [Field K] (w : List (Fin r)) (i : Fin r) :
    firstCoefficient A hs hp b s K w i≠0 := by
  intro hz
  have hF : fieldRoot D K true i=0 := by
    apply (CFSGAlgebraConjugationAction.action K
      (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
      (wordUnit A hs hp b s K w)).injective
    simpa only [map_zero] using hz
  have hentry := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K=>
    M (Sum.inl (s i)) (Sum.inr (s i:Roots A))) hF
  dsimp only at hentry
  rw [field_F_unit_entry] at hentry
  exact one_ne_zero hentry

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeWordCoefficients
