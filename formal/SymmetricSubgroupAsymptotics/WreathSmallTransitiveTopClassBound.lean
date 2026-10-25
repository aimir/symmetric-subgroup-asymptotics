import SymmetricSubgroupAsymptotics.WreathRegularSmallTopClassBound
import SymmetricSubgroupAsymptotics.WreathRestrictedTopClassBound
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-! Full wreath bounds with the literal transitive two- or three-point
top. The three-point symmetric case uses the actual normal alternating
top preimage and its index two, not a subgroup class comparison. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.WreathSmallTransitiveTopClassBound

variable {C I : Type} [Group C] [Finite C] [Finite I]

private theorem full_three_class_card_le (hI : Nat.card I = 3) :
    Nat.card (ConjClasses (PermutationalWreathProduct C (Equiv.Perm I) I)) ≤
      2 * (Nat.card (ConjClasses C) ^ 3 + 2 * Nat.card (ConjClasses C)) := by
  letI : Fintype I := Fintype.ofFinite _
  letI : Nontrivial I := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPretransitive (alternatingGroup I) I :=
    alternatingGroup.isPretransitive_of_three_le_card I hI.ge
  have hR : Nat.card (alternatingGroup I) = 3 := by
    rw [nat_card_alternatingGroup,hI]
    decide +kernel
  have h := WreathRegularSmallTopClassBound.triple_class_card_le (C := C) hR hI
  have hc := WreathRestrictedTopClassBound.class_card_le_restricted_mul_index
    (C := C) (I := I) (alternatingGroup I)
  rw [alternatingGroup.index_eq_two] at hc
  exact hc.trans ((Nat.mul_le_mul_right 2 h).trans_eq (Nat.mul_comm _ _))

theorem pair_class_card_le (T : Subgroup (Equiv.Perm I))
    [MulAction.IsPretransitive T I] (hI : Nat.card I = 2) :
    Nat.card (ConjClasses (PermutationalWreathProduct C T I)) ≤
      Nat.card (ConjClasses C) ^ 2 + Nat.card (ConjClasses C) := by
  let i : I := (Finite.equivFinOfCardEq hI).symm 0
  have hlo : Nat.card I ≤ Nat.card T :=
    Nat.card_le_card_of_surjective (fun g : T => g • i)
      (fun j => MulAction.exists_smul_eq T i j)
  have hhi := T.card_le_card_group
  rw [Nat.card_perm,hI] at hhi
  have hT : Nat.card T = 2 := by norm_num at hhi; omega
  exact WreathRegularSmallTopClassBound.pair_class_card_le hT hI

theorem triple_class_card_le (T : Subgroup (Equiv.Perm I))
    [MulAction.IsPretransitive T I] (hI : Nat.card I = 3) :
    Nat.card (ConjClasses (PermutationalWreathProduct C T I)) ≤
      2 * (Nat.card (ConjClasses C) ^ 3 + 2 * Nat.card (ConjClasses C)) := by
  let i : I := (Finite.equivFinOfCardEq hI).symm 0
  have hhi := T.card_le_card_group
  rw [Nat.card_perm,hI] at hhi
  have hmul := (MulAction.stabilizer T i).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive T i,hI] at hmul
  have hp : 0 < Nat.card T := Nat.card_pos
  have hcases : Nat.card T = 3 ∨ Nat.card T = 6 := by norm_num at hhi; omega
  rcases hcases with hT | hT
  · exact (WreathRegularSmallTopClassBound.triple_class_card_le (C := C) hT hI).trans
      (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
  · have ht : T = ⊤ := T.eq_top_of_card_eq (by rw [Nat.card_perm,hI,hT]; decide)
    subst T
    let e := (WreathRestrictedTopClassBound.topPreimageEquiv
      (C := C) (I := I) (⊤ : Subgroup (Equiv.Perm I))).trans
      ((MulEquiv.subgroupCongr (Subgroup.comap_top _)).trans Subgroup.topEquiv)
    exact (conjugacyClass_card_congr e).le.trans (full_three_class_card_le hI)

end SymmetricSubgroupAsymptotics.WreathSmallTransitiveTopClassBound
