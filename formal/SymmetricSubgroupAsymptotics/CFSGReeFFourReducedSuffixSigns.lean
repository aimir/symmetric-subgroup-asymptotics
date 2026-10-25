import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylPositivePartMonotonicity
import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeelingWords
import SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu

/-! Reduced alternating relative words retain every surviving positive
root under terminal suffixes. Only one terminal deletion is checked per
length, in eight separately bounded integer certificates on the existing
complete E6 root menu. All suffixes then follow by induction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourReducedSuffixSigns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylIntersectionFactor CFSGNormTwoCoordinateFiniteRootMenu
open CFSGNormTwoCoordinateWeylPositivePartMonotonicity
open CFSGReeFFourInversionPeelingWords
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local instance : DecidableEq (Roots A) := Classical.decEq _

private def vectorWord : List (Fin 6) → (Fin 6 → ℤ) → (Fin 6 → ℤ)
  | [], x => x
  | i :: w, x => vectorWord w x -
      integerPairing A (vectorWord w x) (Pi.single i 1) • Pi.single i 1

private theorem wordRoot_val_eq (w : List (Fin 6)) (k : Roots A) :
    (wordRoot A hs hp b₀ s₀ w k).val = vectorWord w k.val := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change ((rootPairing A hs hp).reflectionPerm (s₀ i)
      (wordRoot A hs hp b₀ s₀ w k)).val = _
    rw [CFSGNormTwoGeckSignedRootColumns.reflection_val, ih]
    rfl

private def tailProperty (head : Bool) (n : ℕ) : Prop :=
  ∀ x ∈ CFSGE6FiniteRootMenu.menu,
    (∀ j, 0 ≤ x j) →
    (∀ j, 0 ≤ vectorWord (suffixWord head (n+1) (n+1)) x j) →
    ∀ j, 0 ≤ vectorWord (suffixWord (!head) n n) x j

private theorem tail_1 : ∀ head : Bool, tailProperty head 0 := by
  unfold tailProperty
  decide +kernel

private theorem tail_2 : ∀ head : Bool, tailProperty head 1 := by
  unfold tailProperty
  decide +kernel

private theorem tail_3 : ∀ head : Bool, tailProperty head 2 := by
  unfold tailProperty
  decide +kernel

private theorem tail_4 : ∀ head : Bool, tailProperty head 3 := by
  unfold tailProperty
  decide +kernel

private theorem tail_5 : ∀ head : Bool, tailProperty head 4 := by
  unfold tailProperty
  decide +kernel

private theorem tail_6 : ∀ head : Bool, tailProperty head 5 := by
  unfold tailProperty
  decide +kernel

private theorem tail_7 : ∀ head : Bool, tailProperty head 6 := by
  unfold tailProperty
  decide +kernel

private theorem tail_8 : ∀ head : Bool, tailProperty head 7 := by
  unfold tailProperty
  decide +kernel

private theorem tail_certificate (head : Bool) (n : Fin 8) :
    tailProperty head n.val := by
  fin_cases n
  · exact tail_1 head
  · exact tail_2 head
  · exact tail_3 head
  · exact tail_4 head
  · exact tail_5 head
  · exact tail_6 head
  · exact tail_7 head
  · exact tail_8 head

private theorem suffix_word_certificate :
    ∀ head : Bool, ∀ n : Fin 8, ∀ k : Fin 9, k.val ≤ n.val →
      suffixWord head (n.val+1) k.val = suffixWord (!head) n.val k.val := by
  decide +kernel

theorem suffixWord_drop (head : Bool) (n : ℕ) (hn : n < 8)
    (k : ℕ) (hk : k ≤ n) :
    suffixWord head (n+1) k = suffixWord (!head) n k :=
  suffix_word_certificate head ⟨n, hn⟩ ⟨k, by omega⟩ hk

theorem successor_tail_positive (head : Bool) (n : Fin 8) (a : PositiveRoot A)
    (ha : ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀
      (suffixWord head (n.val+1) (n.val+1)) a.val).val j) :
    ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ (suffixWord (!head) n.val n.val) a.val).val j := by
  have hm : a.val.val ∈ CFSGE6FiniteRootMenu.menu :=
    root_mem_menu A hd hs hp ho CFSGE6FiniteRootMenu.menu
      CFSGE6FiniteRootMenu.negative_simple_mem CFSGE6FiniteRootMenu.reflection_closed a.val
  rw [wordRoot_val_eq] at ha ⊢
  exact tail_certificate head n a.val.val hm a.property ha

private theorem all_suffix_by_length :
    ∀ n : ℕ, n ≤ 8 → ∀ head : Bool, ∀ k ≤ n, ∀ a : PositiveRoot A,
      (∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ (suffixWord head n n) a.val).val j) →
      ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ (suffixWord head n k) a.val).val j := by
  intro n
  induction n with
  | zero =>
    intro hn head k hk a ha
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst k
    exact ha
  | succ n ih =>
    intro hn head k hk a ha
    by_cases hkn : k = n+1
    · subst k
      exact ha
    · have hk' : k ≤ n := by omega
      have hn' : n < 8 := by omega
      have ht := successor_tail_positive head ⟨n, hn'⟩ a ha
      have hrest := ih (by omega) (!head) k hk' a ht
      rw [suffixWord_drop head n hn' k hk']
      exact hrest

theorem reduced_suffix_positive (n : ℕ) (hn : n ≤ 8) (head : Bool)
    (k : ℕ) (hk : k ≤ n) (a : PositiveRoot A)
    (ha : ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ (suffixWord head n n) a.val).val j) :
    ∀ j, 0 ≤ (wordRoot A hs hp b₀ s₀ (suffixWord head n k) a.val).val j :=
  all_suffix_by_length n hn head k hk a ha

theorem reduced_positive_part_le (K : Type) [Field K] [Finite K]
    (n : ℕ) (hn : n ≤ 8) (head : Bool) (k : ℕ) (hk : k ≤ n) :
    wordSignPart A hd hs hp ho K (suffixWord head n n) false ≤
      wordSignPart A hd hs hp ho K (suffixWord head n k) false :=
  positive_part_le_of_root_implication A hd hs hp ho K
    (suffixWord head n n) (suffixWord head n k)
    (reduced_suffix_positive n hn head k hk)

end SymmetricSubgroupAsymptotics.CFSGReeFFourReducedSuffixSigns
