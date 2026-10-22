import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization
import SymmetricSubgroupAsymptotics.CFSGMatrixFlagPowerDiagonal

/-! Every actual defining-characteristic power element of the soluble
envelope belongs to the positive subgroup. Its diagonal factor is
removed by Frobenius; no whole-group order formula is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelPowerElements
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelFactorization CFSGNormTwoGeckHeightSupport
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem positive_le_unipotent (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (e : (b.support⊕Roots A)≃Fin (Fintype.card (b.support⊕Roots A)))
    (he : ∀i j,weight A hs hp b height j<weight A hs hp b height i→e i<e j) :
    rootGroup A hs hp b s K false≤CFSGMatrixFlagSubgroups.unipotentUnits e := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  exact CFSGWeightedRootPGroup.mem_unipotent_of_weight (weight A hs hp b height) e he
    (canonicalRoot (realizationData A hs hp b s) K false i t)
    (CFSGWeightedRootPGroup.quadratic_identity_on_nonincreasing _ _ _ _ t
      (canonicalRoot_val (realizationData A hs hp b s) K false i t)
      (field_E_strict A hs hp b s height hheight K i)
      (field_second_strict A hs hp b s height hheight K i))

theorem power_element_mem_positive (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈borelEnvelope A hs hp b s K) (k : ℕ) (hk : g^(p^k)=1) :
    g∈rootGroup A hs hp b s K false := by
  obtain ⟨e,he⟩ := CFSGFiniteWeightFlag.exists_flag (weight A hs hp b height)
  obtain ⟨u,hu,t,ht,hgval⟩ := borel_factor A hs hp b s K g hg
  have hu' := positive_le_unipotent A hs hp b s height hheight K e he hu
  obtain ⟨d,hd⟩ := torus_diagonal_of_mem A hs hp b s K t ht
  have httri : (t : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K).BlockTriangular e := by
    rw [hd]
    exact Matrix.blockTriangular_diagonal _
  have hgtri : (g : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K).BlockTriangular e := by
    rw [hgval,Units.val_mul]
    exact hu'.1.mul httri
  have hpow : (g : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)^(p^k)=1 := by
    simpa only [Units.val_pow_eq_pow_val,Units.val_one] using
      congrArg (fun x : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ=>
        (x : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)) hk
  have hd1 (i : b.support⊕Roots A) : (d i:K)=1 := by
    have hi := CFSGMatrixFlagSubgroups.diagonal_one_of_prime_power e p
      (g : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) hgtri k hpow i
    rw [hgval,Units.val_mul,CFSGMatrixFlagSubgroups.upper_diag_mul e hu'.1 httri,
      hu'.2 i,one_mul,hd,Matrix.diagonal_apply_eq] at hi
    exact hi
  have ht1 : t=1 := by
    apply Units.ext
    rw [hd]
    ext i j
    simp [Matrix.diagonal_apply,Matrix.one_apply,hd1]
  rw [ht1,mul_one] at hgval
  exact hgval.symm ▸ hu

theorem pSubgroup_le_positive (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : Subgroup ((Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ))
    (hP : IsPGroup p P) (hPB : P≤borelEnvelope A hs hp b s K) :
    P≤rootGroup A hs hp b s K false := by
  intro g hg
  obtain ⟨k,hk⟩ := hP ⟨g,hg⟩
  have hpow : g^(p^k)=1 := congrArg P.subtype hk
  exact power_element_mem_positive A hs hp b s height hheight K p g (hPB hg) k hpow

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelPowerElements
