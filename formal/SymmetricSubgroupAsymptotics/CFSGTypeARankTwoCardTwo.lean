import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearGcdCardComparison
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.NormNum

/-! The actual rank-two type-A model over any two-element field has
order 168. Every proper subgroup has index at least seven: its faithful
simple-group coset action embeds the group into a symmetric group, and
seven divides the group order. No small-group isomorphism or subgroup
census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo

open CFSGTypeAGeneralLinearCardBound CFSGProjectiveLinearGcdCardComparison
open PrimitiveSocleRawStructure

theorem projective_card_eq_168 (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 168 := by
  letI : Fintype F := Fintype.ofFinite F
  letI : Finite (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Finite.of_injective (fun A : Matrix.SpecialLinearGroup (Fin 3) F => A.val)
      Subtype.val_injective
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) F) = 168 := by
    rw [Matrix.card_GL_field]
    have hc : Fintype.card F = 2 := by simpa only [Nat.card_eq_fintype_card] using hF
    rw [hc]
    norm_num [Fin.prod_univ_three]
  have hu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  have hlo : 168 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) := by
    have hh := generalLinear_card_le_specialLinear_mul_units (F := F) (n := Fin 3)
    simpa only [hGL, hu, mul_one] using hh
  have hhi : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) ≤ 168 := by
    have hh := Nat.card_le_card_of_injective
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 3) F →
        Matrix.GeneralLinearGroup (Fin 3) F) Matrix.SpecialLinearGroup.toGL_injective
    simpa only [hGL] using hh
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := Nat.le_antisymm hhi hlo
  have hZ : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) = 1 := by
    have hh := specialLinear_center_card_eq_gcd (F := F) (I := Fin 3)
    exact hh.trans (by rw [hF, Fintype.card_fin]; decide)
  have hh := (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)).card_mul_index
  change Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) *
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) at hh
  simpa only [hZ, one_mul, hSL] using hh

theorem order_eq_168 (q : CFSG.PrimePower) (hq : q.order = 2) :
    Nat.card (CFSG.Models.A 2 q) = 168 :=
  projective_card_eq_168 q.Field (q.card_field.trans hq)

theorem prime_le_proper_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (p : ℕ) (hp : Nat.Prime p) (hdiv : p ∣ Nat.card G)
    (H : Subgroup G) (hH : H ≠ ⊤) : p ≤ H.index := by
  have hcore : H.normalCore = ⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact False.elim (hH (top_unique (ht ▸ H.normalCore_le)))
  have hf : Function.Injective (MulAction.toPermHom G (G ⧸ H)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← Subgroup.normalCore_eq_ker, hcore]
  have hd := Subgroup.card_dvd_of_injective (MulAction.toPermHom G (G ⧸ H)) hf
  rw [Nat.card_perm, ← H.index_eq_card] at hd
  exact hp.dvd_factorial.mp (hdiv.trans hd)

theorem proper_index_ge_seven (q : CFSG.PrimePower) (hq : q.order = 2)
    [IsSimpleGroup (CFSG.Models.A 2 q)] (H : Subgroup (CFSG.Models.A 2 q)) (hH : H ≠ ⊤) :
    7 ≤ H.index := by
  apply prime_le_proper_index 7 (by decide) _ H hH
  rw [order_eq_168 q hq]
  decide

theorem leastProperIndex_ge_seven (q : CFSG.PrimePower) (hq : q.order = 2)
    [IsSimpleGroup (CFSG.Models.A 2 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.A 2 q) ell) : 7 ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact proper_index_ge_seven q hq H hH

end SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo
