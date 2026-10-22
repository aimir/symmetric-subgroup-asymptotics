import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylDegreeTransport

/-! Actual matrix support of a full original Weyl word is its literal
integral lattice action. This assertion does not infer degrees from
coefficient-field eigenvalues. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckWeylDegreeTransport
open CFSGGradedMatrixSupport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem word_lattice_support (K : Type) [Field K] (w : List (Fin r)) :
    Supported (latticeWeight A hs hp b) (wordLinear A hs hp b s w)
      (wordUnit A hs hp b s K w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  induction w with
  | nil=>exact supported_one (latticeWeight A hs hp b)
  | cons i w ih=>
    have hh := supported_mul (weyl_lattice_support A hs hp b s K i) ih
    exact hh

theorem word_preserves_lattice_of_linear_identity (K : Type) [Field K]
    (w : List (Fin r)) (hw : wordLinear A hs hp b s w=1) :
    Supported (latticeWeight A hs hp b) id
      (wordUnit A hs hp b s K w : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) := by
  have hh := word_lattice_support A hs hp b s K w
  rw [hw] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
