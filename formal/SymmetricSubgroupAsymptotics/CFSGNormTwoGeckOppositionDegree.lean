import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticUnit
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns

/-! The original opposition reverses the entire lattice degree of a
quadratic word and exchanges actual positive/negative membership. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionDegree
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckFieldOpposition CFSGNormTwoGeckOppositionWeyl
open CFSGNormTwoGeckSignedRootColumns CFSGNormTwoGeckPositivePGroup
open CFSGGradedMatrixSupport CFSGGradedQuadraticUnit
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def negationEquiv : (n→ℤ)≃+(n→ℤ) where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := neg_add

theorem opposition_lattice_support (K : Type) [Field K] :
    Supported (latticeWeight A hs hp b) (negationEquiv (n:=n))
      (oppositionUnit A hs hp b K : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  intro j k hjk
  change ((CFSGGeckIntegralMatrices.Omega b j k:ℤ):K)=0
  rcases j with j|j <;> rcases k with k|k
  · have hne : j≠k := by
      intro h
      subst k
      exact hjk rfl
    simp [CFSGGeckIntegralMatrices.Omega,hne]
  · simp [CFSGGeckIntegralMatrices.Omega]
  · simp [CFSGGeckIntegralMatrices.Omega]
  · by_cases h : j=(rootPairing A hs hp).reflectionPerm k k
    · subst j
      exfalso
      apply hjk
      change ((rootPairing A hs hp).reflectionPerm k k).val= -k.val
      rw [reflection_val,k.property]
      module
    · simp [CFSGGeckIntegralMatrices.Omega,h]

theorem opposition_quadraticGrade (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : QuadraticGrade (latticeWeight A hs hp b) d g) :
    QuadraticGrade (latticeWeight A hs hp b) (-d)
      (oppositionUnit A hs hp b K*g*(oppositionUnit A hs hp b K)⁻¹) := by
  apply conjugate (latticeWeight A hs hp b) d (negationEquiv (n:=n)) _ _
    (opposition_lattice_support A hs hp b K) _ hg
  simpa only [opposition_inverse] using opposition_lattice_support A hs hp b K

theorem opposition_twice (K : Type) [Field K]
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
    oppositionUnit A hs hp b K*
      (oppositionUnit A hs hp b K*g*(oppositionUnit A hs hp b K)⁻¹)*
        (oppositionUnit A hs hp b K)⁻¹=g := by
  calc
    _=(oppositionUnit A hs hp b K)⁻¹*
        (oppositionUnit A hs hp b K*g*(oppositionUnit A hs hp b K)⁻¹)*
          oppositionUnit A hs hp b K := by simp only [opposition_inverse]
    _=g := by group

theorem opposition_mem_iff (K : Type) [Field K] (neg : Bool)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
    oppositionUnit A hs hp b K*g*(oppositionUnit A hs hp b K)⁻¹∈
        rootGroup A hs hp b s K (!neg) ↔g∈rootGroup A hs hp b s K neg := by
  constructor
  · intro hg
    have hh := opposition_conjugate_mem A hs hp b s K (!neg) _ hg
    simpa only [Bool.not_not,opposition_twice] using hh
  · exact opposition_conjugate_mem A hs hp b s K neg g

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionDegree
