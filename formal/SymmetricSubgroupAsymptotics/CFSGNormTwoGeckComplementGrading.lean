import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylHeightBlocks
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixConjugation
import SymmetricSubgroupAsymptotics.CFSGComplementGradingFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementNormalizer

/-! Detecting the actual positive complement and simple-root factor by
a grading zero on that simple root and positive on the others. The
premises specify only a literal lattice functional. They do not assume
the arbitrary-Weyl positive-root collecting theorem still needed later. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementGrading
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveComplement
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoGeckArbitraryHeightSupport
open CFSGNormTwoGeckWeylHeightBlocks CFSGSerreQuadraticMatrix
open CFSGGradedMatrixSubgroups CFSGComplementGradingFactor
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem complement_le_strict (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] :
    positiveComplement A hs hp b s K i≤strictUnits (weight A hs hp b height) := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨⟨⟨j,hij⟩,t⟩,rfl⟩|⟨⟨⟨j,hij⟩,t⟩,rfl⟩)
  · exact canonicalRoot_strict A hs hp b s height K j t (hother j hij)
  · exact preserving_conjugate_strict _ _ _
      (weyl_preserves A hs hp b s height K i hi)
      (canonicalRoot_strict A hs hp b s height K j t (hother j hij))

theorem simple_le_preserving (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0) (K : Type) [Field K] :
    canonicalRootSubgroup (realizationData A hs hp b s) K false i≤
      preservingUnits (weight A hs hp b height) := by
  rintro g ⟨t,rfl⟩
  exact canonicalRoot_preserves A hs hp b s height K i t hi

theorem positive_mem_complement_of_strict (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hstrict : g∈strictUnits (weight A hs hp b height)) :
    g∈positiveComplement A hs hp b s K i := by
  obtain ⟨v,hv,t,he⟩ := positive_factor A hs hp b s K i g hg
  exact mem_left_of_factor
    (complement_le_strict A hs hp b s height i hi hother K)
    (simple_le_preserving A hs hp b s height i hi K)
    (strict_inf_preserving (weight A hs hp b height)) hv
    (canonicalRoot_mem_subgroup _ K false i t) he hstrict

theorem positive_mem_simple_of_preserves (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hpreserves : g∈preservingUnits (weight A hs hp b height)) :
    g∈canonicalRootSubgroup (realizationData A hs hp b s) K false i := by
  obtain ⟨v,hv,t,he⟩ := positive_factor A hs hp b s K i g hg
  exact mem_right_of_factor
    (complement_le_strict A hs hp b s height i hi hother K)
    (simple_le_preserving A hs hp b s height i hi K)
    (strict_inf_preserving (weight A hs hp b height)) hv
    (canonicalRoot_mem_subgroup _ K false i t) he hpreserves

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementGrading
