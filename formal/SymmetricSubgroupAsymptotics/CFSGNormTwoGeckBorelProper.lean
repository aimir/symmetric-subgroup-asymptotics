import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelPowerElements
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns

/-! Actual nontrivial negative-root elements lie outside the positive
torus envelope. The witness is the Cartan/positive-root matrix entry,
whose coefficient is one even in characteristics two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelProper
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelFactorization CFSGNormTwoGeckBorelPowerElements
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckParameterTripleColumns
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem borel_lower_weight_zero (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈borelEnvelope A hs hp b s K) (j k : b.support⊕Roots A)
    (hjk : weight A hs hp b height j<weight A hs hp b height k) :
    (g : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) j k=0 := by
  obtain ⟨e,he⟩ := CFSGFiniteWeightFlag.exists_flag (weight A hs hp b height)
  obtain ⟨u,hu,t,ht,hgval⟩ := borel_factor A hs hp b s K g hg
  have hu' := positive_le_unipotent A hs hp b s height hheight K e he hu
  obtain ⟨d,hd⟩ := torus_diagonal_of_mem A hs hp b s K t ht
  rw [hgval,Units.val_mul,hd,Matrix.mul_diagonal,hu'.1 (he k j hjk),zero_mul]

theorem negative_root_not_borel (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (i : Fin r) (a : K) (ha : a≠0) :
    canonicalRoot (realizationData A hs hp b s) K true i a∉borelEnvelope A hs hp b s K := by
  intro hg
  have hz := borel_lower_weight_zero A hs hp b s height hheight K _ hg
    (.inl (s i)) (.inr (s i:Roots A)) (by simp only [weight,hheight]; omega)
  have hc := congrFun (negative_positive A hs hp b s K i a) (.inl (s i))
  have he : (canonicalRoot (realizationData A hs hp b s) K true i a : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K) (.inl (s i)) (.inr (s i:Roots A))=a := by
    simpa [Matrix.mulVec_single_one,Pi.single_apply] using hc
  exact ha (he.symm.trans hz)

theorem borel_ne_canonical (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (i : Fin r) :
    borelEnvelope A hs hp b s K≠canonicalElementaryGroup (realizationData A hs hp b s) K := by
  intro h
  have hm := (canonicalElementaryRoot (realizationData A hs hp b s) K true i 1).property
  change canonicalRoot (realizationData A hs hp b s) K true i 1∈
    canonicalElementaryGroup (realizationData A hs hp b s) K at hm
  rw [←h] at hm
  exact negative_root_not_borel A hs hp b s height hheight K i 1 one_ne_zero hm

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelProper
