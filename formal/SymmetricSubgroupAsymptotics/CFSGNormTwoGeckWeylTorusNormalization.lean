import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSignedRootColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoReflectedPairing
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelNormalization
import SymmetricSubgroupAsymptotics.CFSGConjugationClosureNormalizer

/-! Actual Weyl normalization of the literal diagonal torus.
The matrix proof checks the original Cartan and signed root columns,
and uses the integral reflection-pairing identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylTorusNormalization
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckDiagonalTorus CFSGNormTwoGeckWeylSquareTorus
open CFSGNormTwoGeckBorelEnvelope CFSGNormTwoGeckSignedRootColumns
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_mul_torus (K : Type) [Field K] (i j : Fin r) (t : Kˣ) :
    canonicalWeyl (realizationData A hs hp b s) K i*parameterTorus A hs hp b s K j t=
      (parameterTorus A hs hp b s K j t*
        parameterTorus A hs hp b s K i (t^(-integerPairing A (s j:Roots A).val (s i:Roots A).val)))*
        canonicalWeyl (realizationData A hs hp b s) K i := by
  apply Units.ext
  change (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (parameterTorus A hs hp b s K j t : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)=
    ((parameterTorus A hs hp b s K j t : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (parameterTorus A hs hp b s K i (t^(-integerPairing A (s j:Roots A).val (s i:Roots A).val)) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*
      (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
  have hcol (k : b.support⊕Roots A) :
      ((canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
        (parameterTorus A hs hp b s K j t : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*ᵥPi.single k 1=
      (((parameterTorus A hs hp b s K j t : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
        (parameterTorus A hs hp b s K i (t^(-integerPairing A (s j:Roots A).val (s i:Roots A).val)) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*
        (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*ᵥPi.single k 1 := by
    cases k with
    | inl k =>
      have hW := parameterWeyl_cartan A hs hp b s K i 1 k
      rw [parameterWeyl_one] at hW
      simp only [←Matrix.mulVec_mulVec,torus_cartan,hW,Matrix.mulVec_sub,Matrix.mulVec_smul]
    | inr k =>
      let q := (rootPairing A hs hp).reflectionPerm (s i) k
      obtain ⟨c,_,hW⟩ := signed_root_column A hs hp b s K i k
      have he := CFSGNormTwoReflectedPairing.reflected_pairing A hs hp (s i) (s j) k
      have hu : t^(integerPairing A (s j:Roots A).val k.val)=
          t^(integerPairing A (s j:Roots A).val q.val)*
            (t^(-integerPairing A (s j:Roots A).val (s i:Roots A).val))^
              (integerPairing A (s i:Roots A).val q.val) := by
        rw [←zpow_mul,←zpow_add]
        congr 1
        simpa only [q,sub_eq_add_neg,neg_mul] using he.symm
      have hf := congrArg (fun u : Kˣ=>(u:K)) hu
      simp only [Units.val_mul,Units.val_zpow_eq_zpow_val] at hf
      dsimp only [q] at hf
      simp only [←Matrix.mulVec_mulVec,torus_root,Matrix.mulVec_smul,hW,
        smul_smul,Units.val_zpow_eq_zpow_val]
      rw [hf]
      module
  ext u v
  have hh := congrFun (hcol v) u
  simpa only [Matrix.mulVec_single_one] using hh

theorem weyl_conjugate_torus_generator (K : Type) [Field K] (i j : Fin r) (t : Kˣ) :
    canonicalWeyl (realizationData A hs hp b s) K i*parameterTorus A hs hp b s K j t*
      (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹=
      parameterTorus A hs hp b s K j t*
        parameterTorus A hs hp b s K i (t^(-integerPairing A (s j:Roots A).val (s i:Roots A).val)) := by
  rw [weyl_mul_torus,mul_assoc,mul_inv_cancel,mul_one]

theorem weyl_conjugate_torus_mem (K : Type) [Field K] (i : Fin r) :
    ∀t∈torusGroup A hs hp b s K,
      canonicalWeyl (realizationData A hs hp b s) K i*t*
        (canonicalWeyl (realizationData A hs hp b s) K i)⁻¹∈torusGroup A hs hp b s K := by
  apply CFSGConjugationClosureNormalizer.conjugate_closure_mem
  rintro _ ⟨⟨j,t⟩,rfl⟩
  rw [weyl_conjugate_torus_generator]
  exact (torusGroup A hs hp b s K).mul_mem
    (Subgroup.subset_closure ⟨(j,t),rfl⟩)
    (Subgroup.subset_closure ⟨(i,t^(-integerPairing A (s j:Roots A).val (s i:Roots A).val)),rfl⟩)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylTorusNormalization
