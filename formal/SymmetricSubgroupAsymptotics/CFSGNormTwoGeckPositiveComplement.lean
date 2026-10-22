import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCollectingCentrality
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCommutingRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareTorus

/-! The actual positive complement relative to a simple root.
Its generators are the other simple positive units and their literal
Weyl conjugates; all are in the original positive group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveComplement
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckOffDiagonalCollecting
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def complementGenerators (K : Type) [Field K] (i : Fin r) :
    Set (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  Set.range (fun z : {j : Fin r // i≠j}×K=>
    canonicalRoot (realizationData A hs hp b s) K false z.1.val z.2) ∪
  Set.range (fun z : {j : Fin r // i≠j}×K=>
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false z.1.val z.2*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)

def positiveComplement (K : Type) [Field K] (i : Fin r) :
    Subgroup (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  Subgroup.closure (complementGenerators A hs hp b s K i)

theorem simple_mem_complement (K : Type) [Field K] (i j : Fin r) (hne : i≠j) (a : K) :
    canonicalRoot (realizationData A hs hp b s) K false j a∈
      positiveComplement A hs hp b s K i :=
  Subgroup.subset_closure (Or.inl ⟨(⟨j,hne⟩,a),rfl⟩)

theorem conjugate_mem_complement (K : Type) [Field K] (i j : Fin r) (hne : i≠j) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈
        positiveComplement A hs hp b s K i :=
  Subgroup.subset_closure (Or.inr ⟨(⟨j,hne⟩,a),rfl⟩)

theorem complement_le_positive (K : Type) [Field K] (i : Fin r) :
    positiveComplement A hs hp b s K i≤rootGroup A hs hp b s K false := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨z,rfl⟩|⟨z,rfl⟩
  · exact Subgroup.subset_closure ⟨(z.1.val,z.2),rfl⟩
  · exact distinct_simple_conjugate_mem_positive A hs hp b s K i z.1.val z.1.property z.2

theorem positive_conjugate_simple_mem (K : Type) [Field K] (i j : Fin r)
    (hne : i≠j) (t a : K) :
    canonicalRoot (realizationData A hs hp b s) K false i t*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹∈
        positiveComplement A hs hp b s K i := by
  rcases cartan_zero_or_neg_one A hs hp b s i j hne with hz|hn
  · rw [CFSGNormTwoGeckCommutingRoots.orthogonal_conjugation A hs hp b s K i j hz t a]
    exact simple_mem_complement A hs hp b s K i j hne a
  · rw [CFSGNormTwoGeckParameterizedCollecting.adjacent_conjugation_factor
      A hs hp b s K i j hn t a]
    exact (positiveComplement A hs hp b s K i).mul_mem
      (conjugate_mem_complement A hs hp b s K i j hne (a*t))
      (simple_mem_complement A hs hp b s K i j hne a)

theorem positive_conjugate_weyl_simple_mem (K : Type) [Field K] (i j : Fin r)
    (hne : i≠j) (t a : K) :
    canonicalRoot (realizationData A hs hp b s) K false i t*
      (canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j a*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)*
      (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹∈
        positiveComplement A hs hp b s K i := by
  rcases cartan_zero_or_neg_one A hs hp b s i j hne with hz|hn
  · rw [CFSGNormTwoGeckOrthogonalCollecting.orthogonal_word A hs hp b s K i j hz a]
    rw [CFSGNormTwoGeckCommutingRoots.orthogonal_conjugation A hs hp b s K i j hz t a]
    exact simple_mem_complement A hs hp b s K i j hne a
  · rw [CFSGNormTwoGeckCollectingCentrality.adjacent_positive_fixed A hs hp b s K i j hn t a]
    exact conjugate_mem_complement A hs hp b s K i j hne a

theorem weyl_conjugate_simple_mem (K : Type) [Field K] (i j : Fin r)
    (hne : i≠j) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈
        positiveComplement A hs hp b s K i :=
  conjugate_mem_complement A hs hp b s K i j hne a

theorem weyl_conjugate_weyl_simple_mem (K : Type) [Field K] (i j : Fin r)
    (hne : i≠j) (a : K) :
    canonicalWeyl (realizationData A hs hp b s) K i*
      (canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j a*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈
        positiveComplement A hs hp b s K i := by
  rcases cartan_zero_or_neg_one A hs hp b s i j hne with hz|hn
  · rw [CFSGNormTwoGeckOrthogonalCollecting.orthogonal_word A hs hp b s K i j hz a]
    exact conjugate_mem_complement A hs hp b s K i j hne a
  · have he :
      canonicalWeyl (realizationData A hs hp b s) K i*
        (canonicalWeyl (realizationData A hs hp b s) K i*
          canonicalRoot (realizationData A hs hp b s) K false j a*
          (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹=
      (canonicalWeyl (realizationData A hs hp b s) K i)^2*
        canonicalRoot (realizationData A hs hp b s) K false j a*
        ((canonicalWeyl (realizationData A hs hp b s) K i)^2)⁻¹ := by
          simp only [pow_two]
          group
    rw [he,CFSGNormTwoGeckWeylSquareTorus.square_conjugate_adjacent A hs hp b s K i j hn a]
    exact simple_mem_complement A hs hp b s K i j hne (-a)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveComplement
