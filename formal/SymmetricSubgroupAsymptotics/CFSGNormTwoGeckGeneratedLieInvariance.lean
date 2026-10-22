import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticLieInvariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! Every original rational Geck Weyl word preserves the SAME generated
matrix Lie algebra. This makes later homogeneous-line arguments apply
to genuine generated-Lie elements, rather than all ambient matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckRationalAdjointStrings
open CFSGNormTwoGeckRationalWeylCollecting CFSGNormTwoGeckWeylWordDegree
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s
local notation "L" => RootPairing.GeckConstruction.lieAlgebra b
local notation "e" => CFSGAlgebraConjugationAction.action ℚ
  (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)

theorem root_mem_generated (neg : Bool) (i : Fin r) : fieldRoot D ℚ neg i∈L := by
  cases neg
  · rw [rational_E_eq]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (s i)
  · rw [rational_F_eq]
    exact RootPairing.GeckConstruction.f_mem_lieAlgebra (s i)

theorem root_action_mem_generated (neg : Bool) (i : Fin r) (a : ℚ)
    (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ) (hx : X∈L) :
    e (canonicalRoot D ℚ neg i a) X∈L :=
  CFSGSerreQuadraticLieInvariance.root_conjugate_mem D L neg i
    (root_mem_generated A hs hp b s neg i) X hx a

theorem weyl_action_mem_generated (i : Fin r)
    (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ) (hx : X∈L) :
    e (canonicalWeyl D ℚ i) X∈L := by
  have h1 := root_action_mem_generated A hs hp b s false i 1 X hx
  have h2 := root_action_mem_generated A hs hp b s true i (-1) _ h1
  have h3 := root_action_mem_generated A hs hp b s false i 1 _ h2
  rw [canonicalWeyl,map_mul,map_mul]
  exact h3

theorem word_action_mem_generated (w : List (Fin r))
    (X : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ) (hx : X∈L) :
    e (wordUnit A hs hp b s ℚ w) X∈L := by
  induction w generalizing X with
  | nil=>rw [wordUnit,map_one];exact hx
  | cons i w ih=>
    rw [wordUnit,map_mul]
    exact weyl_action_mem_generated A hs hp b s i _ (ih X hx)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance
