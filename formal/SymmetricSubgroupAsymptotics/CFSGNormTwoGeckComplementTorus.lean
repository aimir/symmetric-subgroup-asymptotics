import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelFactorization

/-! The actual soluble Borel envelope normalizes the actual positive
complement. Its whole group has complement/root/torus factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementTorus
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveComplement
open CFSGNormTwoGeckComplementNormalizer CFSGNormTwoGeckOffDiagonalCollecting
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckTorusConjugation
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckTorusHom
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem torus_conjugate_simple_mem (K : Type) [Field K] (i j k : Fin r)
    (hne : i≠j) (t : Kˣ) (a : K) :
    parameterTorus A hs hp b s K k t*
      canonicalRoot (realizationData A hs hp b s) K false j a*
      (parameterTorus A hs hp b s K k t)⁻¹∈positiveComplement A hs hp b s K i := by
  rw [torus_conjugate_positive]
  exact simple_mem_complement A hs hp b s K i j hne _

theorem torus_conjugate_weyl_simple_mem (K : Type) [Field K] (i j k : Fin r)
    (hne : i≠j) (t : Kˣ) (a : K) :
    parameterTorus A hs hp b s K k t*
      (canonicalWeyl (realizationData A hs hp b s) K i*
        canonicalRoot (realizationData A hs hp b s) K false j a*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹)*
      (parameterTorus A hs hp b s K k t)⁻¹∈positiveComplement A hs hp b s K i := by
  rcases cartan_zero_or_neg_one A hs hp b s i j hne with hz|hn
  · rw [CFSGNormTwoGeckOrthogonalCollecting.orthogonal_word A hs hp b s K i j hz a]
    exact torus_conjugate_simple_mem A hs hp b s K i j k hne t a
  · rw [←CFSGNormTwoGeckPositiveCollecting.adjacent_word A hs hp b s K i j hn a]
    have he : ∀h u v : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ,
        h*(u*v*u⁻¹*v⁻¹)*h⁻¹=
          (h*u*h⁻¹)*(h*v*h⁻¹)*(h*u*h⁻¹)⁻¹*(h*v*h⁻¹)⁻¹ := by
      intro h u v
      group
    rw [he,torus_conjugate_positive,torus_conjugate_positive]
    rw [CFSGNormTwoGeckParameterizedCollecting.adjacent_word A hs hp b s K i j hn]
    exact conjugate_mem_complement A hs hp b s K i j hne _

theorem torus_conjugate_mem (K : Type) [Field K] (i k : Fin r) (t : Kˣ) :
    ∀x∈positiveComplement A hs hp b s K i,
      parameterTorus A hs hp b s K k t*x*(parameterTorus A hs hp b s K k t)⁻¹∈
        positiveComplement A hs hp b s K i := by
  apply CFSGConjugationClosureNormalizer.conjugate_closure_mem
  intro x hx
  rcases hx with ⟨z,rfl⟩|⟨z,rfl⟩
  · exact torus_conjugate_simple_mem A hs hp b s K i z.1.val k z.1.property t z.2
  · exact torus_conjugate_weyl_simple_mem A hs hp b s K i z.1.val k z.1.property t z.2

theorem torus_mem_normalizer (K : Type) [Field K] (i k : Fin r) (t : Kˣ) :
    parameterTorus A hs hp b s K k t∈
      Subgroup.normalizer (positiveComplement A hs hp b s K i : Set _) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact torus_conjugate_mem A hs hp b s K i k t x
  · intro hx
    have hh := torus_conjugate_mem A hs hp b s K i k t⁻¹
      (parameterTorus A hs hp b s K k t*x*(parameterTorus A hs hp b s K k t)⁻¹) hx
    simpa only [←parameterTorus_inverse,inv_inv,mul_assoc,inv_mul_cancel,
      inv_mul_cancel_left,one_mul,mul_one] using hh

theorem positive_le_complement_normalizer (K : Type) [Field K] (i : Fin r) :
    rootGroup A hs hp b s K false≤
      Subgroup.normalizer (positiveComplement A hs hp b s K i : Set _) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨j,a⟩,rfl⟩
  by_cases hij : i=j
  · subst j
    exact simple_mem_normalizer A hs hp b s K i a
  · exact (positiveComplement A hs hp b s K i).le_normalizer
      (simple_mem_complement A hs hp b s K i j hij a)

theorem borel_le_complement_normalizer (K : Type) [Field K] (i : Fin r) :
    borelEnvelope A hs hp b s K≤
      Subgroup.normalizer (positiveComplement A hs hp b s K i : Set _) := by
  apply sup_le (positive_le_complement_normalizer A hs hp b s K i)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨k,t⟩,rfl⟩
  exact torus_mem_normalizer A hs hp b s K i k t

theorem borel_factor (K : Type) [Field K] (i : Fin r)
    (g : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hg : g∈borelEnvelope A hs hp b s K) :
    ∃v∈positiveComplement A hs hp b s K i,∃a : K,
      ∃t∈torusGroup A hs hp b s K,
        g=v*canonicalRoot (realizationData A hs hp b s) K false i a*t := by
  obtain ⟨u,hu,t,ht,rfl⟩ := CFSGNormTwoGeckBorelFactorization.borel_factor A hs hp b s K g hg
  obtain ⟨v,hv,a,rfl⟩ := positive_factor A hs hp b s K i u hu
  exact ⟨v,hv,a,t,ht,rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementTorus
