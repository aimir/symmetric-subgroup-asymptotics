import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! Literal root-reflection words and their conjugated root units belong
to the original canonical elementary matrix group. No abstract Weyl-group
recognition or extra positive-root membership premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordMembership
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGSerreQuadraticMatrix
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem word_mem (K : Type) [Field K] (w : List (Fin r)) :
    wordUnit A hs hp b s K w∈canonicalElementaryGroup (realizationData A hs hp b s) K := by
  let G := canonicalElementaryGroup (realizationData A hs hp b s) K
  induction w with
  | nil=>exact G.one_mem
  | cons i w ih=>
    apply G.mul_mem _ ih
    change canonicalRoot (realizationData A hs hp b s) K false i 1*
      canonicalRoot (realizationData A hs hp b s) K true i (-1)*
        canonicalRoot (realizationData A hs hp b s) K false i 1∈G
    exact G.mul_mem (G.mul_mem
      (canonicalElementaryRoot (realizationData A hs hp b s) K false i 1).property
      (canonicalElementaryRoot (realizationData A hs hp b s) K true i (-1)).property)
      (canonicalElementaryRoot (realizationData A hs hp b s) K false i 1).property

theorem word_root_conjugate_mem (K : Type) [Field K] (w : List (Fin r))
    (neg : Bool) (j : Fin r) (a : K) :
    wordUnit A hs hp b s K w*canonicalRoot (realizationData A hs hp b s) K neg j a*
      (wordUnit A hs hp b s K w)⁻¹∈
        canonicalElementaryGroup (realizationData A hs hp b s) K := by
  let G := canonicalElementaryGroup (realizationData A hs hp b s) K
  have hw := word_mem A hs hp b s K w
  exact G.mul_mem (G.mul_mem hw
    (canonicalElementaryRoot (realizationData A hs hp b s) K neg j a).property) (G.inv_mem hw)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootWordMembership
