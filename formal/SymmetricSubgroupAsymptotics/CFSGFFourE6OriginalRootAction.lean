import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeParabolics
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction

/-! Any automorphism of ORIGINAL simple F4 admits an inner adjustment
preserving the opposed Sylows and permuting the actual four simple root
charts. Intrinsic opposite-parabolic intersections provide the charts.
This does not assume that the automorphism lifts to the matrix source,
or that it preserves root lengths in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootAction
open CFSGFFourE6OriginalOppositeParabolics CFSGFFourE6OriginalRootIntersection
open CFSGFFourE6OriginalPairAlignment CFSGFFourE6OriginalOppositeAlignment
open CFSGFFourE6OriginalProjection CFSGMinimalOvergroupAutomorphismAction
open CFSG.Models.Chevalley

theorem exists_original_opposite_parabolic_permutation (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hV : (originalNegative K).map f.toMonoidHom = originalNegative K) :
    ∃ sigma : Equiv.Perm (Fin 4), ∀ a : Fin 4,
      (originalOppositeParabolic K a).map f.toMonoidHom = originalOppositeParabolic K (sigma a) := by
  have hB : (Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K))).map
      f.toMonoidHom = Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K)) :=
    (Subgroup.map_equiv_normalizer_eq (originalNegative K) f).trans
      (congrArg (fun S : Subgroup (Projective CartanMatrix.F₄ K) =>
        Subgroup.normalizer (S : Set (Projective CartanMatrix.F₄ K))) hV)
  exact exists_minimal_overgroup_permutation
    (Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K)))
    (originalOppositeParabolic K) (original_lower_lt_oppositeParabolic K p)
    (original_oppositeParabolic_minimal K p) (original_minimal_overgroup_eq_oppositeParabolic K p)
    (originalOppositeParabolic_injective K p) f hB

theorem exists_original_root_permutation (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map f.toMonoidHom =
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)))
    (hV : (originalNegative K).map f.toMonoidHom = originalNegative K) :
    ∃ sigma : Equiv.Perm (Fin 4), ∀ a : Fin 4,
      (originalOrbitRoot K a).map f.toMonoidHom = originalOrbitRoot K (sigma a) := by
  obtain ⟨sigma, hsigma⟩ := exists_original_opposite_parabolic_permutation K p f hV
  refine ⟨sigma, fun a => ?_⟩
  rw [← original_positive_inf_oppositeParabolic K p a,
    Subgroup.map_inf _ _ _ f.injective, hU, hsigma a, original_positive_inf_oppositeParabolic K p]

theorem exists_inner_fix_pair_and_root_permutation (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K)) :
    ∃ (g : Projective CartanMatrix.F₄ K) (sigma : Equiv.Perm (Fin 4)),
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map
        (MulAut.conj g * f).toMonoidHom = (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) ∧
      (originalNegative K).map (MulAut.conj g * f).toMonoidHom = originalNegative K ∧
      ∀ a : Fin 4, (originalOrbitRoot K a).map (MulAut.conj g * f).toMonoidHom =
        originalOrbitRoot K (sigma a) := by
  obtain ⟨g, hU, hV⟩ := original_exists_inner_fix_pair K p f
  obtain ⟨sigma, hsigma⟩ := exists_original_root_permutation K p (MulAut.conj g * f) hU hV
  exact ⟨g, sigma, hU, hV, hsigma⟩

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootAction
