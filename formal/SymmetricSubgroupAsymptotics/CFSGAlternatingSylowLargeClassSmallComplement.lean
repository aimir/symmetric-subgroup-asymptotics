import SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupSmallComplement
import SymmetricSubgroupAsymptotics.CFSGNormalTwoGroupTranspositionClasses
import Mathlib.GroupTheory.Sylow
import SymmetricSubgroupAsymptotics.CFSGPermutationSubsetExtension

/-! An alternating Sylow two-subgroup in degree at least six cannot have
a normalizer transposition class with at most one outside point. Restriction
is faithful and normal in the full class symmetric group; normal two-group
triviality contradicts the actual nontrivial Sylow order. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSylowLargeClassSmallComplement
open Equiv Equiv.Perm CFSGNormalizerTranspositionClasses
open CFSGNormalTwoGroupSmallComplement

theorem alternating_card_even {X : Type*} [Fintype X] [DecidableEq X]
    (hsize : 4 ≤ Nat.card X) : 2 ∣ Nat.card (alternatingGroup X) := by
  have hc : 1 < Fintype.card X := by
    simpa only [Nat.card_eq_fintype_card] using (show 1 < Nat.card X by omega)
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp hc
  have hd : 4 ∣ Nat.factorial (Nat.card X) :=
    (show 4 ∣ Nat.factorial 4 by decide).trans (Nat.factorial_dvd_factorial hsize)
  obtain ⟨m, hm⟩ := hd
  rw [nat_card_alternatingGroup, hm]
  exact ⟨m, by omega⟩

theorem sylow_image_ne_bot {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (hsize : 4 ≤ Nat.card X) :
    (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype ≠ ⊥ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := P.ne_bot_of_dvd_card (alternating_card_even hsize)
  intro he
  apply hP
  apply bot_unique
  intro x hx
  change x = 1
  apply Subtype.ext
  have hm : x.val ∈ (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype :=
    ⟨x, hx, rfl⟩
  rw [he] at hm
  exact hm

theorem impossible {X : Type*} [Fintype X] [DecidableEq X]
    (P : Sylow 2 (alternatingGroup X)) (hsize : 6 ≤ Nat.card X) (x : X)
    (hcompl : ((pointClass (Subgroup.normalizer
      (((P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype) : Set (Perm X))) x)ᶜ).ncard ≤ 1) :
    False := by
  let P0 := (P : Subgroup (alternatingGroup X)).map (alternatingGroup X).subtype
  let N := Subgroup.normalizer (P0 : Set (Perm X))
  let s := pointClass N x
  have hsmall : (sᶜ : Set X).ncard ≤ 1 := hcompl
  have hs5 : 5 ≤ Nat.card s := by
    rw [Nat.card_coe_set_eq]
    have hsum := Set.ncard_add_ncard_compl s
    omega
  have hs3 : 2 < s.ncard := by
    have h := hs5
    rw [Nat.card_coe_set_eq] at h
    omega
  have hP0 : IsPGroup 2 P0 := P.isPGroup'.map (alternatingGroup X).subtype
  have hPs : P0 ≤ MulAction.stabilizer (Perm X) s := by
    intro g hg
    apply MulAction.mem_stabilizer_iff.mpr
    change g '' s = s
    exact CFSGNormalTwoGroupTranspositionClasses.preserves_large_class P0 hP0 x hs3 g hg
  have hN : ∀ t : Perm s, CFSGPermutationSubsetProduct.splitEmbedding s (t, 1) ∈
      Subgroup.normalizer (P0 : Set (Perm X)) := by
    intro t
    rw [CFSGPermutationSubsetProduct.splitEmbedding_fst_eq_ofSubtype]
    exact class_symmetric_range_le N x ⟨t, rfl⟩
  have hbot : P0 = ⊥ := eq_bot_of_normal_restriction P0 hP0 s hPs hs5
    (Set.ncard_le_one_iff_subsingleton.mp hsmall) hN
  exact sylow_image_ne_bot P (by omega) hbot

end SymmetricSubgroupAsymptotics.CFSGAlternatingSylowLargeClassSmallComplement
