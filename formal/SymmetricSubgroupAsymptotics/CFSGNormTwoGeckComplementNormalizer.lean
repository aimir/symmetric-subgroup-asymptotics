import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveComplement
import SymmetricSubgroupAsymptotics.CFSGConjugationClosureNormalizer
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootSubgroup
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Actual collecting decomposition relative to one simple root.
The complement is normalized by that root subgroup and its Weyl word,
and the WHOLE original positive group factors as complement times root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveComplement
open CFSGConjugationClosureNormalizer
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem positive_conjugate_mem (K : Type) [Field K] (i : Fin r) (t : K) :
    ∀x∈positiveComplement A hs hp b s K i,
      canonicalRoot (realizationData A hs hp b s) K false i t*x*
        (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹∈
          positiveComplement A hs hp b s K i := by
  apply conjugate_closure_mem
  intro x hx
  rcases hx with ⟨z,rfl⟩|⟨z,rfl⟩
  · exact positive_conjugate_simple_mem A hs hp b s K i z.1.val z.1.property t z.2
  · exact positive_conjugate_weyl_simple_mem A hs hp b s K i z.1.val z.1.property t z.2

theorem simple_mem_normalizer (K : Type) [Field K] (i : Fin r) (t : K) :
    canonicalRoot (realizationData A hs hp b s) K false i t∈
      Subgroup.normalizer (positiveComplement A hs hp b s K i : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact positive_conjugate_mem A hs hp b s K i t x
  · intro hx
    have hh := positive_conjugate_mem A hs hp b s K i (-t)
      (canonicalRoot (realizationData A hs hp b s) K false i t*x*
        (canonicalRoot (realizationData A hs hp b s) K false i t)⁻¹) hx
    simpa only [←canonicalRoot_inverse,inv_inv,mul_assoc,inv_mul_cancel,
      inv_mul_cancel_left,one_mul,mul_one] using hh

theorem weyl_conjugate_mem (K : Type) [Field K] (i : Fin r) :
    ∀x∈positiveComplement A hs hp b s K i,
      canonicalWeyl (realizationData A hs hp b s) K i*x*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈
          positiveComplement A hs hp b s K i := by
  apply conjugate_closure_mem
  intro x hx
  rcases hx with ⟨z,rfl⟩|⟨z,rfl⟩
  · exact weyl_conjugate_simple_mem A hs hp b s K i z.1.val z.1.property z.2
  · exact weyl_conjugate_weyl_simple_mem A hs hp b s K i z.1.val z.1.property z.2

theorem weyl_mem_normalizer (K : Type) [Field K] (i : Fin r) :
    canonicalWeyl (realizationData A hs hp b s) K i∈
      Subgroup.normalizer (positiveComplement A hs hp b s K i : Set _) :=
  mem_normalizer_of_conjugate_closed_of_pow_one _ _
    (weyl_conjugate_mem A hs hp b s K i) 4 (by decide)
    (CFSGNormTwoGeckWeylUnits.weyl_four A hs hp b s K i)

theorem single_root_le_positive (K : Type) [Field K] (i : Fin r) :
    canonicalRootSubgroup (realizationData A hs hp b s) K false i≤
      rootGroup A hs hp b s K false := by
  rintro x ⟨a,rfl⟩
  exact Subgroup.subset_closure ⟨(i,a),rfl⟩

theorem single_root_le_complement_normalizer (K : Type) [Field K] (i : Fin r) :
    canonicalRootSubgroup (realizationData A hs hp b s) K false i≤
      Subgroup.normalizer (positiveComplement A hs hp b s K i : Set _) := by
  rintro x ⟨a,rfl⟩
  exact simple_mem_normalizer A hs hp b s K i a

theorem positive_eq_complement_sup_root (K : Type) [Field K] (i : Fin r) :
    rootGroup A hs hp b s K false=
      positiveComplement A hs hp b s K i ⊔
        canonicalRootSubgroup (realizationData A hs hp b s) K false i := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨j,a⟩,rfl⟩
    by_cases hij : i=j
    · subst j
      exact (show canonicalRootSubgroup (realizationData A hs hp b s) K false i≤
        positiveComplement A hs hp b s K i ⊔
          canonicalRootSubgroup (realizationData A hs hp b s) K false i from le_sup_right)
        (canonicalRoot_mem_subgroup _ K false i a)
    · exact (show positiveComplement A hs hp b s K i≤
        positiveComplement A hs hp b s K i ⊔
          canonicalRootSubgroup (realizationData A hs hp b s) K false i from le_sup_left)
        (simple_mem_complement A hs hp b s K i j hij a)
  · exact sup_le (complement_le_positive A hs hp b s K i)
      (single_root_le_positive A hs hp b s K i)

theorem positive_factor (K : Type) [Field K] (i : Fin r)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false) :
    ∃v∈positiveComplement A hs hp b s K i,∃a : K,
      g=v*canonicalRoot (realizationData A hs hp b s) K false i a := by
  rw [positive_eq_complement_sup_root A hs hp b s K i] at hg
  change g∈((positiveComplement A hs hp b s K i ⊔
    canonicalRootSubgroup (realizationData A hs hp b s) K false i : Subgroup _) : Set _) at hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (single_root_le_complement_normalizer A hs hp b s K i)] at hg
  rcases hg with ⟨v,hv,u,hu,he⟩
  rcases hu with ⟨a,rfl⟩
  exact ⟨v,hv,a,he.symm⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementNormalizer
