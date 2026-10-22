import SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupTranspositionClasses
import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowOddNormalizerLift
import SymmetricSubgroupAsymptotics.CFSGAlternatingSylowProperRestriction
import SymmetricSubgroupAsymptotics.CFSGPermutationSubsetExtension
import SymmetricSubgroupAsymptotics.CFSGSymmetricSylowNotNormal

/-! An alternating Sylow normalizer cannot have a transposition class
of size at least three with at least two points outside it. The class
restriction is both a symmetric Sylow and normal in its full symmetric
group, contradicting the checked symmetric self-normalizer theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingNormalizerProperLargeClass
open Equiv Perm CFSGNormalizerTranspositionClasses CFSGPermutationSubsetProduct

theorem impossible {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (x : X)
    (hsize : 3 ≤ (pointClass (Subgroup.normalizer
      (((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) : Set (Perm X))) x).ncard)
    (hcomp : 2 ≤ Nat.card ((pointClass (Subgroup.normalizer
      (((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) : Set (Perm X))) x)ᶜ : Set X)) :
    False := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H := (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype
  let N := Subgroup.normalizer (H : Set (Perm X))
  let C := pointClass N x
  have hH : IsPGroup 2 H := P.isPGroup'.map (alternatingGroup X).subtype
  have hHC : H ≤ MulAction.stabilizer (Perm X) C := by
    intro g hg
    apply MulAction.mem_stabilizer_iff.mpr
    change g '' C = C
    have hlarge : 2 < (pointClass (Subgroup.normalizer (H : Set (Perm X))) x).ncard := by
      change 2 < (pointClass (Subgroup.normalizer
        (((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) : Set (Perm X))) x).ncard
      omega
    exact CFSGNormalTwoGroupTranspositionClasses.preserves_large_class H hH x hlarge g hg
  have hN : ∀ a : Perm C, splitEmbedding C (a, 1) ∈ N := by
    intro a
    rw [splitEmbedding_fst_eq_ofSubtype]
    exact class_symmetric_range_le N x ⟨a, rfl⟩
  have hcsize : 3 ≤ Nat.card C := by simpa only [Nat.card_coe_set_eq] using hsize
  haveI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne C
  let t := splitEmbedding C (Equiv.swap a b, (1 : Perm (Cᶜ : Set X)))
  have htodd : t ∉ alternatingGroup X := by
    intro ht
    have hh := mem_alternatingGroup.mp ht
    change sign (splitEmbedding C (Equiv.swap a b, 1)) = 1 at hh
    rw [sign_splitEmbedding, sign_swap hab, map_one, mul_one] at hh
    norm_num at hh
  have ht2 : t ^ 2 = 1 := by
    change splitEmbedding C (Equiv.swap a b, (1 : Perm (Cᶜ : Set X))) ^ 2 = 1
    rw [← map_pow]
    simp only [pow_two, Prod.mk_mul_mk, Equiv.swap_mul_self, mul_one]
    exact (splitEmbedding C).map_one
  obtain ⟨Q, hPQ, hQC⟩ := CFSGAlternatingSylowOddNormalizerLift.exists_symmetricSylow_between
    P (MulAction.stabilizer (Perm X) C) hHC t (splitEmbedding_fst_mem_stabilizer C _)
    htodd ht2 (hN _)
  have hnormal := CFSGPermutationNormalRestriction.restriction_range_normal H C hHC hN
  have hrange := CFSGAlternatingSylowProperRestriction.range_eq_restrictedSylow P Q hPQ C hQC hcomp
  have hnormal' :
      (CFSGPermutationSylowRestriction.restrictedSylow Q C hQC : Subgroup (Perm C)).Normal := by
    rwa [← hrange]
  exact CFSGSymmetricSylowNotNormal.not_normal hcsize _ hnormal'

end SymmetricSubgroupAsymptotics.CFSGAlternatingNormalizerProperLargeClass
