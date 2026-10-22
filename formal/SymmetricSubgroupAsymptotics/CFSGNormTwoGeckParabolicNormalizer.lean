import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRankOneParabolicProof
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelProper

/-! The actual positive-subgroup normalizer INSIDE each simple-root
parabolic is exactly the original Borel. The ambient/global normalizer
is not identified by this local statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParabolicNormalizer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoGeckBorelNormalization
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_not_normalizer (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (i : Fin r) :
    canonicalWeyl (realizationData A hs hp b s) K i∉
      Subgroup.normalizer (rootGroup A hs hp b s K false : Set _) := by
  intro hN
  have hu : canonicalRoot (realizationData A hs hp b s) K false i 1∈
      rootGroup A hs hp b s K false := Subgroup.subset_closure ⟨(i,1),rfl⟩
  have hh := (Subgroup.mem_normalizer_iff.mp hN _).mp hu
  rw [CFSGNormTwoGeckSelfRootConjugation.self_root_word] at hh
  have hUB : rootGroup A hs hp b s K false≤borelEnvelope A hs hp b s K := le_sup_left
  exact CFSGNormTwoGeckBorelProper.negative_root_not_borel A hs hp b s height hheight
    K i (-1) (neg_ne_zero.mpr one_ne_zero) (hUB hh)

theorem normalizer_inter_parabolic_le_borel (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (i : Fin r) :
    Subgroup.normalizer (rootGroup A hs hp b s K false : Set _) ⊓
      Subgroup.closure ((borelEnvelope A hs hp b s K : Set _)∪
        {canonicalWeyl (realizationData A hs hp b s) K i})≤borelEnvelope A hs hp b s K := by
  intro g hg
  rcases CFSGNormTwoGeckRankOneParabolicProof.parabolic_cover A hs hp b s K i g hg.2 with
    hB|⟨x,hx,u,hu,he⟩
  · exact hB
  · let N : Subgroup (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
      Subgroup.normalizer (rootGroup A hs hp b s K false : Set _)
    have hxN : x∈N := borelEnvelope_le_normalizer_positive A hs hp b s K hx
    have huN : u∈N := (rootGroup A hs hp b s K false).le_normalizer hu
    have hgN : g∈N := hg.1
    have hxi : x⁻¹∈N := N.inv_mem hxN
    have hui : u⁻¹∈N := N.inv_mem huN
    have hprod : x⁻¹*g*u⁻¹∈N := N.mul_mem (N.mul_mem hxi hgN) hui
    have hw : canonicalWeyl (realizationData A hs hp b s) K i=
        x⁻¹*g*u⁻¹ := by rw [he]; group
    have hwN : canonicalWeyl (realizationData A hs hp b s) K i∈
        Subgroup.normalizer (rootGroup A hs hp b s K false : Set _) := by
      rw [hw]
      exact hprod
    exact False.elim (weyl_not_normalizer A hs hp b s height hheight K i hwN)

theorem normalizer_inter_parabolic_eq_borel (height : (n→ℤ)→ₗ[ℤ]ℤ)
    (hheight : ∀i : b.support,height (i:Roots A).val=1)
    (K : Type) [Field K] (i : Fin r) :
    Subgroup.normalizer (rootGroup A hs hp b s K false : Set _) ⊓
      Subgroup.closure ((borelEnvelope A hs hp b s K : Set _)∪
        {canonicalWeyl (realizationData A hs hp b s) K i})=borelEnvelope A hs hp b s K := by
  apply le_antisymm (normalizer_inter_parabolic_le_borel A hs hp b s height hheight K i)
  intro g hg
  exact ⟨borelEnvelope_le_normalizer_positive A hs hp b s K hg,
    Subgroup.subset_closure (Or.inl hg)⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParabolicNormalizer
