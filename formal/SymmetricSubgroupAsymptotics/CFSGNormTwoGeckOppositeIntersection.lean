import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOpposite
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadraticMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelProper

/-! Actual U+ and U- have trivial intersection. A parameter-one simple
root is nontrivial in every field, proved through its original opposite
root column rather than a characteristic-zero eigenvalue argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckArbitraryHeightSupport CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckQuadraticMembership
open CFSGNormTwoGeckOppositionDegree CFSGNormTwoGeckFieldOpposition
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckSelfRootConjugation
open CFSGSerreQuadraticMatrix CFSGGradedMatrixSubgroups CFSGGradedQuadraticUnit
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem positive_le_strict (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1) (K : Type) [Field K] :
    rootGroup A hs hp b s K false≤strictUnits (weight A hs hp b height) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨⟨i,t⟩,rfl⟩
  exact canonicalRoot_strict A hs hp b s height K i t (by rw [hheight];exact zero_lt_one)

theorem negative_le_strict_opposite (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1) (K : Type) [Field K] :
    rootGroup A hs hp b s K true≤strictUnits (fun j=> -weight A hs hp b height j) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨⟨i,t⟩,rfl⟩
  have hpos := canonicalRoot_quadraticGrade A hs hp b s K i t
  have hneg := opposition_quadraticGrade A hs hp b K (s i:Roots A).val _ hpos
  rw [canonicalRoot_conjugate] at hneg
  have hh := quadratic_strict A hs hp b (-height) K (-(s i:Roots A).val) _ hneg
    (by simp only [LinearMap.neg_apply,map_neg,neg_neg,hheight];exact zero_lt_one)
  have he : weight A hs hp b (-height)=(fun j=> -weight A hs hp b height j) := by
    funext j
    cases j <;> rfl
  simpa only [he] using hh

theorem positive_inf_negative (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1) (K : Type) [Field K] :
    rootGroup A hs hp b s K false⊓rootGroup A hs hp b s K true=⊥ := by
  apply le_antisymm _ bot_le
  exact (inf_le_inf (positive_le_strict A hs hp b s height hheight K)
    (negative_le_strict_opposite A hs hp b s height hheight K)).trans
      (le_of_eq (strict_inf_opposite (weight A hs hp b height)))

theorem canonicalRoot_one_ne_one (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1) (K : Type) [Field K] (i : Fin r) :
    canonicalRoot (realizationData A hs hp b s) K false i 1≠1 := by
  intro he
  have hh := self_root_word A hs hp b s K i 1
  rw [he,mul_one,mul_inv_cancel] at hh
  have hB : canonicalRoot (realizationData A hs hp b s) K true i (-1)∈
      borelEnvelope A hs hp b s K := by
    rw [←hh]
    exact (borelEnvelope A hs hp b s K).one_mem
  exact CFSGNormTwoGeckBorelProper.negative_root_not_borel A hs hp b s height hheight
    K i (-1) (neg_ne_zero.mpr one_ne_zero) hB

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
