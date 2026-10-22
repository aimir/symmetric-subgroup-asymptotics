import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylTorusNormalization

/-! Every literal Weyl word normalizes the SAME actual diagonal torus.
This includes inverse conjugation, with no ambient finiteness premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordTorus
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylUnits
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckWeylTorusNormalization
open CFSGConjugationClosureNormalizer
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_mem_torus_normalizer (K : Type) [Field K] (i : Fin r) :
    canonicalWeyl (realizationData A hs hp b s) K i∈
      Subgroup.normalizer (torusGroup A hs hp b s K : Set _) :=
  mem_normalizer_of_conjugate_closed_of_pow_one _ _
    (weyl_conjugate_torus_mem A hs hp b s K i) 4 (by decide)
    (weyl_four A hs hp b s K i)

theorem wordUnit_mem_torus_normalizer (K : Type) [Field K] (w : List (Fin r)) :
    wordUnit A hs hp b s K w∈Subgroup.normalizer (torusGroup A hs hp b s K : Set _) := by
  let N : Subgroup (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
    Subgroup.normalizer (torusGroup A hs hp b s K : Set _)
  change wordUnit A hs hp b s K w∈N
  induction w with
  | nil=>exact N.one_mem
  | cons i w ih=>
    exact N.mul_mem (weyl_mem_torus_normalizer A hs hp b s K i) ih

theorem word_inverse_torus_mem (K : Type) [Field K] (w : List (Fin r))
    (t : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (ht : t∈torusGroup A hs hp b s K) :
    (wordUnit A hs hp b s K w)⁻¹*t*wordUnit A hs hp b s K w∈torusGroup A hs hp b s K := by
  let N : Subgroup (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
    Subgroup.normalizer (torusGroup A hs hp b s K : Set _)
  have hn : wordUnit A hs hp b s K w∈N := wordUnit_mem_torus_normalizer A hs hp b s K w
  have hi : (wordUnit A hs hp b s K w)⁻¹∈N := N.inv_mem hn
  have hh := (Subgroup.mem_normalizer_iff.mp hi t).mp ht
  simpa only [inv_inv] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordTorus
