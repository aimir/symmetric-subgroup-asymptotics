import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusConjugation

/-! The actual positive subgroup is normal in its literal soluble torus
envelope. This is the forward containment B ≤ N(U); the reverse
containment, needed for the Sylow-normalizer theorem, remains open. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelNormalization
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckTorusConjugation
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem torus_mem_normalizer_positive (K : Type) [Field K] (i : Fin r) (t : Kˣ) :
    parameterTorus A hs hp b s K i t∈Subgroup.normalizer
      (rootGroup A hs hp b s K false : Set
        ((Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)) := by
  apply Subgroup.normalizer_le_normalizer_closure
    (Set.range (fun z : Fin r×K=>canonicalRoot (realizationData A hs hp b s) K false z.1 z.2))
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  ext x
  constructor
  · rintro ⟨y,⟨⟨j,a⟩,rfl⟩,rfl⟩
    refine ⟨(j,a*(t:K)^(integerPairing A (s i:Roots A).val (s j:Roots A).val)),?_⟩
    exact (torus_conjugate_positive A hs hp b s K i j t a).symm
  · rintro ⟨⟨j,a⟩,rfl⟩
    let c : K := (t:K)^(integerPairing A (s i:Roots A).val (s j:Roots A).val)
    have hc : c≠0 := zpow_ne_zero _ (Units.ne_zero t)
    refine ⟨canonicalRoot (realizationData A hs hp b s) K false j (a/c),⟨(j,a/c),rfl⟩,?_⟩
    change parameterTorus A hs hp b s K i t*
      canonicalRoot (realizationData A hs hp b s) K false j (a/c)*
        (parameterTorus A hs hp b s K i t)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K false j a
    rw [torus_conjugate_positive]
    change canonicalRoot (realizationData A hs hp b s) K false j ((a/c)*c)=_
    rw [div_mul_cancel₀ a hc]

theorem borelEnvelope_le_normalizer_positive (K : Type) [Field K] :
    borelEnvelope A hs hp b s K≤Subgroup.normalizer
      (rootGroup A hs hp b s K false : Set
        ((Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)) := by
  apply sup_le
  · exact (rootGroup A hs hp b s K false).le_normalizer
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨i,t⟩,rfl⟩
    exact torus_mem_normalizer_positive A hs hp b s K i t

theorem positive_normal_in_borelEnvelope (K : Type) [Field K] :
    ((rootGroup A hs hp b s K false).subgroupOf (borelEnvelope A hs hp b s K)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (show
    rootGroup A hs hp b s K false≤borelEnvelope A hs hp b s K from le_sup_left)).mpr
  exact borelEnvelope_le_normalizer_positive A hs hp b s K

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelNormalization
