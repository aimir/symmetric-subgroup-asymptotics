import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelNormalization
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Literal positive-times-torus factorization of the soluble envelope.
Every torus element is a genuine diagonal unit; no uniqueness or
Sylow-normalizer containment is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckDiagonalTorus
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelNormalization CFSGDiagonalMatrixUnits
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem torusGroup_le_diagonal (K : Type) [Field K] :
    torusGroup A hs hp b s K≤(diagonalHom (b.support⊕Roots A) K).range := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  refine ⟨(fun k=>t^(weight A hs hp b s i k)),?_⟩
  apply Units.ext
  rw [diagonalHom_val,torus_diagonal]
  congr 1
  funext k
  exact Units.val_zpow_eq_zpow_val t _

theorem torus_diagonal_of_mem (K : Type) [Field K]
    (t : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (ht : t∈torusGroup A hs hp b s K) :
    ∃d : b.support⊕Roots A→Kˣ,
      (t : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)=
        Matrix.diagonal (fun i=>(d i:K)) := by
  obtain ⟨d,hd⟩ := torusGroup_le_diagonal A hs hp b s K ht
  refine ⟨d,?_⟩
  rw [←hd]
  rfl

theorem borel_factor (K : Type) [Field K]
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈borelEnvelope A hs hp b s K) :
    ∃u∈rootGroup A hs hp b s K false,∃t∈torusGroup A hs hp b s K,g=u*t := by
  have hT : torusGroup A hs hp b s K≤Subgroup.normalizer
      (rootGroup A hs hp b s K false : Set
        ((Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)) :=
    le_trans le_sup_right (borelEnvelope_le_normalizer_positive A hs hp b s K)
  have he := Subgroup.coe_mul_of_right_le_normalizer_left
    (rootGroup A hs hp b s K false) (torusGroup A hs hp b s K) hT
  change g∈(↑(rootGroup A hs hp b s K false⊔torusGroup A hs hp b s K) : Set _) at hg
  rw [he] at hg
  obtain ⟨u,hu,t,ht,heq⟩ := hg
  exact ⟨u,hu,t,ht,heq.symm⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
