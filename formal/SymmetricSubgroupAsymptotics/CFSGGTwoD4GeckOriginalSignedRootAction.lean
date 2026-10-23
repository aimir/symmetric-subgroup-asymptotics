import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOppositionAxes
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalRankOneWitness
import SymmetricSubgroupAsymptotics.CFSGOpposedFamilyPermutation
import SymmetricSubgroupAsymptotics.CFSGSignedSubgroupPermutationAgreement

/-! The same Bool permutation acts on both signs of the actual
original simple G2 ranges. Opposition supplies positive recognition;
cross-sign commutation matches the two permutations. The possible
characteristic-three type swap is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSignedRootAction
open CFSGGTwoD4GeckOriginalNegativeRootAction CFSGGTwoD4GeckOriginalOppositionAxes
open CFSGGTwoD4GeckOriginalRankOneWitness CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalOppositeAlignment
open CFSGOpposedFamilyPermutation CFSGSignedSubgroupPermutationAgreement CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

theorem exists_original_signed_root_permutation (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MulAut (Projective CartanMatrix.G₂ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)).map
      f.toMonoidHom = (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)))
    (hV : (originalNegative K).map f.toMonoidHom = originalNegative K) :
    ∃ sigma : Equiv.Perm Bool, ∀ (isNegative a : Bool),
      (originalSimpleHom K isNegative a).range.map f.toMonoidHom =
        (originalSimpleHom K isNegative (sigma a)).range := by
  let R := fun a => (originalSimpleHom K false a).range
  let N := fun a => (originalSimpleHom K true a).range
  obtain ⟨sigma, hsigma⟩ := exists_opposite_family_permutation
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K))
    (originalNegative K) R N (MulAut.conj (originalOpposition K))
    (original_positive_opposition_map K p) (original_negative_opposition_map K p)
    (original_negative_axis_opposition_map K) (exists_original_negative_root_permutation K p) f hU hV
  obtain ⟨tau, htau⟩ := exists_original_negative_root_permutation K p f hU hV
  have heq : sigma = tau := permutations_agree R N
    (by
      intro i j hij x hx y hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact original_distinct_opposite_commute K i j hij a b)
    (by
      intro i
      exact ⟨originalSimpleHom K false i (Multiplicative.ofAdd 1), ⟨_, rfl⟩,
        originalSimpleHom K true i (Multiplicative.ofAdd 1), ⟨_, rfl⟩,
        original_same_axis_not_commute K p i⟩) f sigma tau hsigma htau
  subst tau
  refine ⟨sigma, ?_⟩
  intro isNegative a
  cases isNegative
  · exact hsigma a
  · exact htau a

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSignedRootAction
