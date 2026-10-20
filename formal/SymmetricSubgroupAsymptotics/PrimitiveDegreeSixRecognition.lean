import SymmetricSubgroupAsymptotics.PGLTwoFiveRecognition
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Finite

/-! Small subgroup recognition used by the primitive degree-six slice.
All identifications are constructed from actual subgroup and coset actions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
open Equiv Subgroup MulAction
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PrimitiveDegreeSixRecognition

theorem card_perm_six : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

/-- An order-60 subgroup of a group identified with S₅ is A₅. -/
def indexTwoEquiv {K : Type*} [Group K] [Finite K]
    (e : K ≃* Equiv.Perm (Fin 5)) (H : Subgroup K) (hH : Nat.card H = 60) :
    H ≃* alternatingGroup (Fin 5) := by
  let J := H.map e.toMonoidHom
  have he := H.equivMapOfInjective e.toMonoidHom e.injective
  have hJ : Nat.card J = 60 := (Nat.card_congr he.toEquiv).symm.trans hH
  have hi : J.index = 2 := by
    have h := J.card_mul_index
    have hp : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    rw [hJ, hp] at h
    omega
  exact he.trans (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))

/-- An order-60 subgroup of A₆ is A₅, using the faithful index-six coset action. -/
def alternatingSubgroupEquiv (H : Subgroup (alternatingGroup (Fin 6)))
    (hH : Nat.card H = 60) : H ≃* alternatingGroup (Fin 5) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hi : H.index = 6 := by
    have h := H.card_mul_index
    rw [hH, card_alt_six] at h
    omega
  have hc : H.normalCore = ⊥ := by
    rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with h | h
    · exact h
    · have ht : H = ⊤ := top_le_iff.mp (h ▸ H.normalCore_le)
      have := hi
      rw [ht, Subgroup.index_top] at this
      omega
  have hf : Function.Injective
      (MulAction.toPermHom (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6) ⧸ H)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← Subgroup.normalCore_eq_ker H, hc]
  let e : (alternatingGroup (Fin 6) ⧸ H) ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, ← H.index_eq_card]; exact hi)
  let f : alternatingGroup (Fin 6) →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6) ⧸ H))
  have hfi : Function.Injective f := e.permCongrHom.injective.comp hf
  let p := e ((1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H)
  let s : Finset (Fin 6) := {p}ᶜ
  have hs : s.card = 5 := by
    change ({p}ᶜ : Finset (Fin 6)).card = 5
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  let j : Equiv.Perm ↥s →* Equiv.Perm (Fin 6) := Equiv.Perm.ofSubtype
  have hji : Function.Injective j := Equiv.Perm.ofSubtype_injective
  have hle : H.map f ≤ j.range := by
    rintro x ⟨h, hh, rfl⟩
    have hfix : h • ((1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H) =
        ((1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H) := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [MulAction.stabilizer_quotient]
      exact hh
    have hfix' : f h p = p := by
      change e ((MulAction.toPermHom (alternatingGroup (Fin 6))
        (alternatingGroup (Fin 6) ⧸ H) h) (e.symm (e _))) = e _
      simp only [Equiv.symm_apply_apply, MulAction.toPermHom_apply,
        MulAction.toPerm_apply, hfix]
    rw [Equiv.Perm.mem_range_ofSubtype_iff]
    intro y hy
    change y ∈ s
    simp only [s, Finset.mem_compl, Finset.mem_singleton]
    intro hyp
    subst y
    exact (Equiv.Perm.mem_support.mp hy) hfix'
  let T := (H.map f).subgroupOf j.range
  have hT : Nat.card T = 60 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      ← Nat.card_congr (H.equivMapOfInjective f hfi).toEquiv]
    exact hH
  let eJ : j.range ≃* Equiv.Perm (Fin 5) :=
    (MonoidHom.ofInjective hji).symm.trans (Finset.equivFinOfCardEq hs).permCongrHom
  exact (H.equivMapOfInjective f hfi).trans <|
    (Subgroup.subgroupOfEquivOfLe hle).symm.trans <| indexTwoEquiv eJ T hT

end SymmetricSubgroupAsymptotics.PrimitiveDegreeSixRecognition
