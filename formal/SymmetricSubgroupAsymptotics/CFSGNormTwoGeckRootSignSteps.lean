import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadraticMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositionDegree
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneCells

/-! Actual sign-change steps for homogeneous quadratic elements in the
positive or negative group. Only a zero excluded height can cross from
one sign to the other; that case is the literal simple-root subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootSignSteps
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckFieldOpposition
open CFSGNormTwoGeckOppositionWeyl CFSGNormTwoGeckOppositionDegree
open CFSGNormTwoGeckQuadraticMembership CFSGNormTwoGeckSelfRootConjugation
open CFSGNormTwoGeckRankOneCells CFSGSerreQuadraticMatrix CFSGGradedQuadraticUnit
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem inverse_self_root_word (K : Type) [Field K] (i : Fin r) (t : K) :
    (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹*
      canonicalRoot (realizationData A hs hp b s) K false i t*
        canonicalWeyl (realizationData A hs hp b s) K i=
      canonicalRoot (realizationData A hs hp b s) K true i (-t) := by
  let w := canonicalWeyl (realizationData A hs hp b s) K i
  let u := canonicalRoot (realizationData A hs hp b s) K false i t
  have hc : w^2*u*(w^2)⁻¹=u := square_conjugate_self A hs hp b s K i t
  have hcomm : w^2*u=u*w^2 := by
    calc
      w^2*u=(w^2*u*(w^2)⁻¹)*w^2 := by group
      _=u*w^2 := by rw [hc]
  change w⁻¹*u*w=_
  calc
    w⁻¹*u*w=w⁻¹*(u*w^2)*w⁻¹ := by simp only [pow_two];group
    _=w⁻¹*(w^2*u)*w⁻¹ := by rw [hcomm]
    _=w*u*w⁻¹ := by simp only [pow_two];group
    _=_ := self_root_word A hs hp b s K i t

theorem positive_flip (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : height d=0) :
    canonicalWeyl (realizationData A hs hp b s) K i*g*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈rootGroup A hs hp b s K true := by
  obtain ⟨t,rfl⟩ := positive_quadratic_mem_simple A hs hp b s height i hi hother K d g hg hgrade hd
  rw [self_root_word]
  exact Subgroup.subset_closure ⟨(i,-t),rfl⟩

theorem positive_inverse_flip (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K false)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : height d=0) :
    (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹*g*
      canonicalWeyl (realizationData A hs hp b s) K i∈rootGroup A hs hp b s K true := by
  obtain ⟨t,rfl⟩ := positive_quadratic_mem_simple A hs hp b s height i hi hother K d g hg hgrade hd
  rw [inverse_self_root_word]
  exact Subgroup.subset_closure ⟨(i,-t),rfl⟩

theorem opposition_conjugate_weyl (K : Type) [Field K] (i : Fin r)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
    oppositionUnit A hs hp b K*
      (canonicalWeyl (realizationData A hs hp b s) K i*g*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)*
      (oppositionUnit A hs hp b K)⁻¹=
    (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹*
      (oppositionUnit A hs hp b K*g*(oppositionUnit A hs hp b K)⁻¹)*
      canonicalWeyl (realizationData A hs hp b s) K i := by
  let w := canonicalWeyl (realizationData A hs hp b s) K i
  let o := oppositionUnit A hs hp b K
  have hw : o*w*o⁻¹=w⁻¹ := opposition_weyl A hs hp b s K i
  have hi : o*w⁻¹*o⁻¹=w := by
    calc
      o*w⁻¹*o⁻¹=(o*w*o⁻¹)⁻¹ := by group
      _=w := by rw [hw,inv_inv]
  change o*(w*g*w⁻¹)*o⁻¹=w⁻¹*(o*g*o⁻¹)*w
  calc
    _=(o*w*o⁻¹)*(o*g*o⁻¹)*(o*w⁻¹*o⁻¹) := by group
    _=_ := by rw [hw,hi]

theorem negative_stays_negative (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K true)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : height d<0) :
    canonicalWeyl (realizationData A hs hp b s) K i*g*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈rootGroup A hs hp b s K true := by
  have hpos := opposition_conjugate_mem A hs hp b s K true g hg
  have hdeg := opposition_quadraticGrade A hs hp b K d g hgrade
  have hd' : 0<height (-d) := by rw [map_neg];omega
  have hh := weyl_inverse_conjugate_positive A hs hp b s height i hi hother K (-d) _ hpos hdeg hd'
  apply (opposition_mem_iff A hs hp b s K true _).mp
  rw [opposition_conjugate_weyl]
  exact hh

theorem negative_flip (height : (n→ℤ)→ₗ[ℤ]ℤ) (i : Fin r)
    (hi : height (s i:Roots A).val=0)
    (hother : ∀j : Fin r,i≠j→0<height (s j:Roots A).val)
    (K : Type) [Field K] (d : n→ℤ)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp b s K true)
    (hgrade : QuadraticGrade (latticeWeight A hs hp b) d g) (hd : height d=0) :
    canonicalWeyl (realizationData A hs hp b s) K i*g*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈rootGroup A hs hp b s K false := by
  have hpos := opposition_conjugate_mem A hs hp b s K true g hg
  have hdeg := opposition_quadraticGrade A hs hp b K d g hgrade
  have hd' : height (-d)=0 := by rw [map_neg,hd,neg_zero]
  have hh := positive_inverse_flip A hs hp b s height i hi hother K (-d) _ hpos hdeg hd'
  apply (opposition_mem_iff A hs hp b s K false _).mp
  rw [opposition_conjugate_weyl]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRootSignSteps
