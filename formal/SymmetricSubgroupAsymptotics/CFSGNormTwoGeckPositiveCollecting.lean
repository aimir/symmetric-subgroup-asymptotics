import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalPositiveCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCollectingTransport

/-! Actual adjacent positive-root collecting over every coefficient
ring. The rational identity is first proved as an equality over ℤ[X],
then evaluated. The group-membership endpoint uses the literal original
positive generators, with no root-group recognition or division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGSerreQuadraticCollectingTransport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem adjacent_word (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j= -1) (a : K) :
    canonicalRoot (realizationData A hs hp b s) K false i 1*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalRoot (realizationData A hs hp b s) K false i 1)⁻¹*
      (canonicalRoot (realizationData A hs hp b s) K false j a)⁻¹=
      canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j a*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹ := by
  exact collecting_word_of_rational (realizationData A hs hp b s) K i j
    (fun a=>CFSGNormTwoGeckRationalPositiveCollecting.adjacent_word A hs hp b s i j hij a) a

theorem adjacent_conjugate_mem_positive (K : Type) [Field K] (i j : Fin r)
    (hij : cartan b s i j= -1) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈rootGroup A hs hp b s K false := by
  rw [←adjacent_word A hs hp b s K i j hij a]
  have hi : canonicalRoot (realizationData A hs hp b s) K false i 1∈
      rootGroup A hs hp b s K false := Subgroup.subset_closure ⟨(i,1),rfl⟩
  have hj : canonicalRoot (realizationData A hs hp b s) K false j a∈
      rootGroup A hs hp b s K false := Subgroup.subset_closure ⟨(j,a),rfl⟩
  exact (rootGroup A hs hp b s K false).mul_mem
    ((rootGroup A hs hp b s K false).mul_mem
      ((rootGroup A hs hp b s K false).mul_mem hi hj)
      ((rootGroup A hs hp b s K false).inv_mem hi))
    ((rootGroup A hs hp b s K false).inv_mem hj)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveCollecting
