import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticOrthogonalCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup

/-! Literal orthogonal simple-root words over every coefficient ring.
The original Serre relations discharge the rational bracket conditions;
integer polynomial transport proves the word identity in all characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckRationalWeylCollecting
open CFSGSerreQuadraticCollectingTransport CFSGNormTwoGeckPositivePGroup
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem indices_ne_of_cartan_zero (i j : Fin r) (hij : cartan b s i j=0) : i≠j := by
  intro h
  subst j
  have hd := b.cartanMatrix_apply_same (s i)
  change cartan b s i i=2 at hd
  omega

theorem orthogonal_word (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j=0) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K false j a := by
  exact CFSGSerreQuadraticOrthogonalCollecting.root_word_of_rational
    (realizationData A hs hp b s) K i j
    (fun a=>CFSGSerreQuadraticOrthogonalCollecting.rational_root_word
      (realizationData A hs hp b s) i j
      (lie_of_cartan_zero A hs hp b s i j hij)
      (F_E_ne A hs hp b s i j (indices_ne_of_cartan_zero A hs hp b s i j hij)) a) a

theorem orthogonal_conjugate_mem_positive (K : Type) [Field K] (i j : Fin r)
    (hij : cartan b s i j=0) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈rootGroup A hs hp b s K false := by
  rw [orthogonal_word A hs hp b s K i j hij a]
  exact Subgroup.subset_closure ⟨(j,a),rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalCollecting
