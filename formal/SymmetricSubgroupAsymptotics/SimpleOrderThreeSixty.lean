import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Elementary index and action consequences for an actual group of
order 360. Simplicity makes every proper coset action faithful, ruling
out indices below six. Seven is excluded by divisibility. An actual
faithful action on six points identifies the group with A6 because its
literal permutation image has index two in S6. No classification of
order-360 groups or exceptional small-field isomorphism is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimpleOrderThreeSixty
variable {G : Type} [Group G] [Finite G]

private theorem proper_coset_injective [IsSimpleGroup G]
    (H : Subgroup G) (hH : H≠⊤) :
    Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
  have hcore : H.normalCore=⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact False.elim (hH (top_unique (ht ▸ H.normalCore_le)))
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← Subgroup.normalCore_eq_ker,hcore]

theorem proper_index_ge_six [IsSimpleGroup G] (hcard : Nat.card G=360)
    (H : Subgroup G) (hH : H≠⊤) : 6≤H.index := by
  by_contra hs
  have hi : H.index≤5 := by omega
  have hc : 360≤H.index.factorial := by
    have hb := Nat.card_le_card_of_injective
      (MulAction.toPermHom G (G ⧸ H)) (proper_coset_injective H hH)
    simpa only [Nat.card_perm,← H.index_eq_card,hcard] using hb
  have hf : H.index.factorial≤120 := by
    simpa only [show Nat.factorial 5=120 by decide] using Nat.factorial_le hi
  omega

theorem proper_index_ne_seven (hcard : Nat.card G=360) (H : Subgroup G) : H.index≠7 := by
  intro he
  have hd := H.index_dvd_card
  rw [hcard,he] at hd
  exact (by decide : ¬7∣360) hd

def equivAlternatingSixOfInjective (hcard : Nat.card G=360)
    (f : G →* Equiv.Perm (Fin 6)) (hf : Function.Injective f) :
    G ≃* alternatingGroup (Fin 6) := by
  let E : G ≃* f.range := MonoidHom.ofInjective hf
  have hR : Nat.card f.range=360 := (Nat.card_congr E.symm.toEquiv).trans hcard
  have hp : Nat.card (Equiv.Perm (Fin 6))=720 := by
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have hi : f.range.index=2 := by
    have hc := f.range.card_mul_index
    rw [hR,hp] at hc
    omega
  exact E.trans (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))

def equivAlternatingSixOfFaithfulAction {X : Type} [Finite X] [MulAction G X]
    [FaithfulSMul G X] (hcard : Nat.card G=360) (hX : Nat.card X=6) :
    G ≃* alternatingGroup (Fin 6) := by
  let e : X ≃ Fin 6 := Finite.equivFinOfCardEq hX
  let f : G →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G X)
  have hf : Function.Injective f :=
    e.permCongrHom.injective.comp (show Function.Injective (MulAction.toPermHom G X) from
      MulAction.toPerm_injective)
  exact equivAlternatingSixOfInjective hcard f hf

def equivAlternatingSixOfIndexSix [IsSimpleGroup G] (hcard : Nat.card G=360)
    (H : Subgroup G) (hH : H≠⊤) (hi : H.index=6) :
    G ≃* alternatingGroup (Fin 6) := by
  let e : (G ⧸ H) ≃ Fin 6 := Finite.equivFinOfCardEq (by
    rw [← H.index_eq_card]
    exact hi)
  let f : G →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  have hf : Function.Injective f := e.permCongrHom.injective.comp (proper_coset_injective H hH)
  exact equivAlternatingSixOfInjective hcard f hf

end SymmetricSubgroupAsymptotics.SimpleOrderThreeSixty
