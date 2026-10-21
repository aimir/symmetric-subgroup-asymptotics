import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryStarCoverage
import Mathlib.SetTheory.Cardinal.Finite

/-! Every original D simple-root parameter is recovered from the
binary pair. Same-side roots follow by star commutators, and both fork
roots occur in the star itself. Scalar specialization uses only card2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryRootCoverage
open Matrix CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryPairElements CFSGOrthogonalDBinaryStarCoverage
open CFSGOrthogonalDBinaryConjugation CFSGOrthogonalDBinaryCyclePermutation
open CFSGSymplecticBinaryArrayMembership
variable {K : Type} [Field K] [CharP K 2]

theorem positive_short_mem (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H)
    (a b : Fin (s + 4)) (hab : a ≠ b) :
    HasArray H (rootArray (Sum.inl a) (Sum.inl b)) := by
  by_cases ha : a = lastIndex s
  · subst a
    have hb : b.val < s + 3 := by
      have hh := b.isLt
      have hn : b.val ≠ s + 3 := fun h => hab (Fin.ext h.symm)
      omega
    exact (all_stars s H hx hW false (⟨b.val, hb⟩ : Fin (s + 3))).1
  · have ha' : a.val < s + 3 := by
      have hh := a.isLt
      have hn : a.val ≠ s + 3 := fun h => ha (Fin.ext h)
      omega
    have hleft : HasArray H (rootArray (Sum.inl a) (Sum.inl (lastIndex s))) := by
      have hp := (all_stars s H hx hW true (⟨a.val, ha'⟩ : Fin (s + 3))).2
      change HasArray H (rootArray (Sum.inr (lastIndex s)) (Sum.inr a)) at hp
      rw [rootArray_paired] at hp
      exact hp
    by_cases hb : b = lastIndex s
    · subst b
      exact hleft
    · have hb' : b.val < s + 3 := by
        have hh := b.isLt
        have hn : b.val ≠ s + 3 := fun h => hb (Fin.ext h)
        omega
      have hright := (all_stars s H hx hW false (⟨b.val, hb'⟩ : Fin (s + 3))).1
      change HasArray H (CFSGOrthogonalDBinaryRotationArrays.shortArray a (lastIndex s)) at hleft
      change HasArray H (CFSGOrthogonalDBinaryRotationArrays.shortArray (lastIndex s) b) at hright
      have hp := hasArray_mul (hasArray_mul (hasArray_mul hleft hright) hleft) hright
      rw [CFSGOrthogonalDBinaryRotationArrays.star_commutator a (lastIndex s) b ha (Ne.symm hb) hab] at hp
      exact hp

theorem chain_root_array (s : ℕ) (neg : Bool) (i : Fin (s + 4)) (hi : i.val + 1 < s + 4) :
    ((rootElement K (s + 4) neg i 1).val : Mat K (s + 4)) =
      rootArray (if neg then Sum.inr i else Sum.inl i)
        (if neg then Sum.inr (⟨i.val + 1, hi⟩ : Fin (s + 4))
          else Sum.inl (⟨i.val + 1, hi⟩ : Fin (s + 4))) := by
  cases neg <;>
    simp [rootElement, rootTransvection, rootMatrix, negative, positive, hi,
      rootArray, paired, Matrix.transpose_sub, Matrix.transpose_single] <;>
      (ext a b; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        sub_eq_add_neg, CharTwo.neg_eq]; abel)

theorem fork_root_array (s : ℕ) (neg : Bool) :
    ((rootElement K (s + 4) neg (lastIndex s) 1).val : Mat K (s + 4)) =
      if neg then rootArray (Sum.inr (lastIndex s)) (Sum.inl (penultimateIndex s))
      else rootArray (Sum.inl (penultimateIndex s)) (Sum.inr (lastIndex s)) := by
  have hi : ¬(lastIndex s).val + 1 < s + 4 := by
    change ¬s + 3 + 1 < s + 4
    omega
  have hp : previous (s + 4) (lastIndex s) = penultimateIndex s := by
    apply Fin.ext
    dsimp [previous, lastIndex, penultimateIndex]
  cases neg <;>
    simp [rootElement, rootTransvection, rootMatrix, negative, positive, hi, hp,
      rootArray, paired, Matrix.transpose_sub, Matrix.transpose_single] <;>
      (ext a b; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
        sub_eq_add_neg, CharTwo.neg_eq]; abel)

theorem all_roots_one_mem (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H)
    (neg : Bool) (i : Fin (s + 4)) : (rootElement K (s + 4) neg i 1).val ∈ H := by
  apply (hasArray_iff_mem H _).mp
  by_cases hi : i.val + 1 < s + 4
  · rw [chain_root_array s neg i hi]
    let j : Fin (s + 4) := ⟨i.val + 1, hi⟩
    have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; change i.val = i.val + 1 at hh; omega
    cases neg
    · exact positive_short_mem s H hx hW i j hij
    · simp only [if_true]
      rw [rootArray_paired]
      exact positive_short_mem s H hx hW j i (Ne.symm hij)
  · have he : i = lastIndex s := by
      apply Fin.ext
      have hb := i.isLt
      change i.val = s + 3
      omega
    subst i
    rw [fork_root_array]
    cases neg
    · simp only [Bool.false_eq_true, if_false]
      have hp := (all_stars s H hx hW true (Fin.last (s + 2))).1
      rw [rootArray_paired] at hp
      exact hp
    · exact (all_stars s H hx hW false (Fin.last (s + 2))).2

theorem all_roots_mem (hcard : Nat.card K = 2) (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H)
    (neg : Bool) (i : Fin (s + 4)) (a : K) : (rootElement K (s + 4) neg i a).val ∈ H := by
  have ha : a = 0 ∨ a = 1 := by
    by_cases hz : a = 0
    · exact Or.inl hz
    · exact Or.inr (((Nat.card_eq_two_iff' (0 : K)).mp hcard).unique hz one_ne_zero)
  rcases ha with rfl | rfl
  · rw [rootElement_zero]
    exact H.one_mem
  · exact all_roots_one_mem s H hx hW neg i

theorem elementary_le_of_pair (hcard : Nat.card K = 2) (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H) :
    elementaryRootGroup K (s + 4) ≤ H := by
  apply (Subgroup.closure_le H).mpr
  rintro g ⟨neg, i, a, rfl⟩
  exact all_roots_mem hcard s H hx hW neg i a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryRootCoverage
