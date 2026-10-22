import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSubgroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeWordCoefficients
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstCoefficient
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootDegreeSeparation

/-! Distinct ORIGINAL root subgroups intersect trivially in every field.
The proof projects onto the literal first root degree, before any possible
bad-characteristic collision of torus eigenvalues. No Lie-image injectivity
or automorphism-invariance premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckIntegralWord CFSGNormTwoGeckNegativeWordCoefficients
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoRootDegreeSeparation
open CFSGGradedMatrixSupport CFSGGradedQuadraticUnit
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedQuadraticFirstCoefficient
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "ell" => latticeWeight A hs hp b₀

theorem eq_one_of_mem_two_roots (K : Type) [Field K] (k l : Roots A) (hkl : k≠l)
    (x : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hx : x∈rootSubgroup A hd hs hp ho K k) (hy : x∈rootSubgroup A hd hs hp ho K l) : x=1 := by
  let p := rootWitness A hd hs hp ho k
  let q := rootWitness A hd hs hp ho l
  change x∈wordRootSubgroup A hd hs hp ho K p.val.1 p.val.2 at hx
  change x∈wordRootSubgroup A hd hs hp ho K q.val.1 q.val.2 at hy
  obtain ⟨a,ha⟩ := (mem_wordRootSubgroup_iff A hd hs hp ho K p.val.1 p.val.2 x).mp hx
  obtain ⟨b,hb⟩ := (mem_wordRootSubgroup_iff A hd hs hp ho K q.val.1 q.val.2 x).mp hy
  have hE := first_support A hs hp b₀ s₀ K p.val.1 p.val.2
  have hD := second_support A hs hp b₀ s₀ K p.val.1 p.val.2
  have hF := first_support A hs hp b₀ s₀ K q.val.1 q.val.2
  have hG := second_support A hs hp b₀ s₀ K q.val.1 q.val.2
  rw [←p.property] at hE hD
  rw [←q.property] at hF hG
  have hleft := word_expansion A hs hp b₀ s₀ K p.val.1 p.val.2 a
  have hright := word_expansion A hs hp b₀ s₀ K q.val.1 q.val.2 b
  have hleft' : (x : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)=
      1+a • firstCoefficient A hs hp b₀ s₀ K p.val.1 p.val.2+
        a^2 • secondCoefficient A hs hp b₀ s₀ K p.val.1 p.val.2 := by
    rw [←ha]
    simpa only [rootWord,word_eq_canonicalWord] using hleft
  have hright' : (x : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)=
      1+b • firstCoefficient A hs hp b₀ s₀ K q.val.1 q.val.2+
        b^2 • secondCoefficient A hs hp b₀ s₀ K q.val.1 q.val.2 := by
    rw [←hb]
    simpa only [rootWord,word_eq_canonicalWord] using hright
  have hz := first_zero_of_distinct_quadratic ell k.val l.val
    (a • firstCoefficient A hs hp b₀ s₀ K p.val.1 p.val.2)
    (a^2 • secondCoefficient A hs hp b₀ s₀ K p.val.1 p.val.2)
    (b • firstCoefficient A hs hp b₀ s₀ K q.val.1 q.val.2)
    (b^2 • secondCoefficient A hs hp b₀ s₀ K q.val.1 q.val.2)
    (supported_smul ell _ _ hE a) (supported_smul ell _ _ hD (a^2))
    (supported_smul ell _ _ hF b) (supported_smul ell _ _ hG (b^2))
    (root_val_ne_zero A k) (root_val_ne_double A k k)
    (root_val_ne_of_ne A k l hkl) (root_val_ne_double A k l) (hleft'.symm.trans hright')
  have ha0 : a=0 := by
    rcases smul_eq_zero.mp hz with ha0 | hz
    · exact ha0
    · exact False.elim ((first_ne_zero A hs hp b₀ s₀ K p.val.1 p.val.2) hz)
  rw [←ha,ha0,rootWord,canonicalRoot_zero,mul_one,mul_inv_cancel]

theorem rootSubgroup_inf_eq_bot (K : Type) [Field K] (k l : Roots A) (hkl : k≠l) :
    rootSubgroup A hd hs hp ho K k⊓rootSubgroup A hd hs hp ho K l=⊥ := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_two_roots A hd hs hp ho K k l hkl x hx.1 hx.2)
  · intro hx
    have hx1 := Subgroup.mem_bot.mp hx
    subst x
    exact ⟨Subgroup.one_mem _,Subgroup.one_mem _⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootIntersection
