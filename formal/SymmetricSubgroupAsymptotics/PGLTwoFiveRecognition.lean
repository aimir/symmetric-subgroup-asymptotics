import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! A small-index recognition argument, independent of matrix groups.
An order-120 subgroup of S₆ has a faithful coset action on six points:
its normal core cannot contain A₆. Its image is a point stabilizer,
and hence is S₅. No finite multiplication table is used. -/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Equiv Subgroup MulAction
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PGLTwoFiveRecognition

private theorem card_six : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

/-- Every subgroup of order 120 in the symmetric group on six points is S₅. -/
def subgroupEquiv (H : Subgroup (Equiv.Perm (Fin 6)))
    (hH : Nat.card H = 120) : H ≃* Equiv.Perm (Fin 5) := by
  classical
  have hindex : H.index = 6 := by
    have h := H.card_mul_index
    rw [hH, card_six] at h
    omega
  have hcore : H.normalCore = ⊥ := by
    by_contra hn
    have hnt : Nontrivial H.normalCore := H.normalCore.nontrivial_iff_ne_bot.mpr hn
    have hA : alternatingGroup (Fin 6) ≤ H :=
      (Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt).trans H.normalCore_le
    have hle := Subgroup.card_le_of_le hA
    have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [hH, hcardA] at hle
    omega
  have hcoset : Function.Injective
      (MulAction.toPermHom (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 6) ⧸ H)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← Subgroup.normalCore_eq_ker H, hcore]
  let e : (Equiv.Perm (Fin 6) ⧸ H) ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, ← H.index_eq_card]; exact hindex)
  let ψ : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom (Equiv.Perm (Fin 6)) (Equiv.Perm (Fin 6) ⧸ H))
  have hψ : Function.Injective ψ := e.permCongrHom.injective.comp hcoset
  let q₀ : Equiv.Perm (Fin 6) ⧸ H := ((1 : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 6) ⧸ H)
  let p₀ : Fin 6 := e q₀
  let s : Finset (Fin 6) := {p₀}ᶜ
  have hs : s.card = 5 := by
    change ({p₀}ᶜ : Finset (Fin 6)).card = 5
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  let ι : Equiv.Perm ↥s →* Equiv.Perm (Fin 6) := Equiv.Perm.ofSubtype
  have hι : Function.Injective ι := Equiv.Perm.ofSubtype_injective
  have hle : H.map ψ ≤ ι.range := by
    rintro x ⟨h, hh, rfl⟩
    have hfix : h • q₀ = q₀ := by
      apply MulAction.mem_stabilizer_iff.mp
      change h ∈ MulAction.stabilizer (Equiv.Perm (Fin 6))
        ((1 : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 6) ⧸ H)
      rw [MulAction.stabilizer_quotient]
      exact hh
    have hfix' : ψ h p₀ = p₀ := by
      change e ((MulAction.toPermHom (Equiv.Perm (Fin 6))
        (Equiv.Perm (Fin 6) ⧸ H) h) (e.symm (e q₀))) = e q₀
      simp only [Equiv.symm_apply_apply, MulAction.toPermHom_apply,
        MulAction.toPerm_apply, hfix]
    rw [Equiv.Perm.mem_range_ofSubtype_iff]
    intro y hy
    change y ∈ s
    simp only [s, Finset.mem_compl, Finset.mem_singleton]
    intro hy0
    subst y
    exact (Equiv.Perm.mem_support.mp hy) hfix'
  have hcardι : Nat.card ι.range = 120 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe, hs]
    decide
  have hmap : H.map ψ = ι.range := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcardι, ← Nat.card_congr (H.equivMapOfInjective ψ hψ).toEquiv, hH]
  exact (H.equivMapOfInjective ψ hψ).trans <|
    (MulEquiv.subgroupCongr hmap).trans <|
      (MonoidHom.ofInjective hι).symm.trans <|
        (Finset.equivFinOfCardEq hs).permCongrHom

end SymmetricSubgroupAsymptotics.PGLTwoFiveRecognition
