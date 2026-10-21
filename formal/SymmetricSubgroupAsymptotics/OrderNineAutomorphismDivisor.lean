import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Tactic.NormNum

/-! Every group of order nine has automorphism order dividing48.
The cyclic case has six automorphisms. Otherwise the actual additive
group is a two-dimensional F3-space and its automorphisms embed in GL2(3).
No multiplication table or abstract group locator is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.OrderNineAutomorphismDivisor

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem proper_divisor_nine :
    ∀ n : Fin 10,n.val ∣ 9 → n.val ≠ 9 → n.val ∣ 3 := by decide +kernel

private theorem gl_two_three_card_receipt :
    (∏ i : Fin 2, ((3 : ℕ)^2-3^i.val))=48 := by decide +kernel

theorem card_aut_dvd_fortyEight {P : Type} [Group P] [Finite P]
    (hP : Nat.card P = 9) : Nat.card (MulAut P) ∣ 48 := by
  by_cases hc : IsCyclic P
  · letI := hc
    rw [IsCyclic.card_mulAut,hP]
    decide +kernel
  have hcomm : ∀ a b : P,a*b=b*a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by simpa using hP)
  letI : CommGroup P := { (inferInstance : Group P) with mul_comm := hcomm }
  have hexp (x : P) : x ^ 3 = 1 := by
    have hd : orderOf x ∣ 9 := hP ▸ orderOf_dvd_natCard x
    have hle : orderOf x ≤ 9 := Nat.le_of_dvd (by decide) hd
    have hne : orderOf x ≠ 9 := by
      intro hx
      exact hc (isCyclic_of_orderOf_eq_card x (hx.trans hP.symm))
    exact orderOf_dvd_iff_pow_eq_one.mp (proper_divisor_nine ⟨orderOf x,by omega⟩ hd hne)
  letI : Module (ZMod 3) (Additive P) :=
    AddCommGroup.zmodModule (n := 3) (fun x => by
      apply Additive.toMul.injective
      change x.toMul ^ 3 = 1
      exact hexp x.toMul)
  letI : Module.Finite (ZMod 3) (Additive P) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 3) (Additive P) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < (3 : ℕ))
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive P)
    have hcard : Nat.card (Additive P) = 9 := hP
    simpa only [Nat.card_zmod,hcard] using h.symm
  let aLin : MulAut P →* (Additive P ≃ₗ[ZMod 3] Additive P) :=
    { toFun := fun a =>
        { a.toAdditive with map_smul' := fun c x => ZMod.map_smul a.toAdditive c x }
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let basis := Module.finBasis (ZMod 3) (Additive P)
  let aGL : MulAut P →* LinearMap.GeneralLinearGroup (ZMod 3) (Additive P) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive P)).symm.toMonoidHom.comp aLin
  let phi : MulAut P →*
      Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 3) (Additive P))) (ZMod 3) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp aGL
  have hphi : Function.Injective phi := by
    intro a b h
    have hGL : aGL a = aGL b := (Matrix.GeneralLinearGroup.toLin' basis).symm.injective h
    have he : aLin a = aLin b :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) (Additive P)).symm.injective hGL
    apply MulEquiv.ext
    intro x
    exact congrArg Additive.toMul (DFunLike.congr_fun he (Additive.ofMul x))
  have hGL : Nat.card
      (Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 3) (Additive P))) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field,hdim]
    simpa only [ZMod.card] using gl_two_three_card_receipt
  exact hGL ▸ Subgroup.card_dvd_of_injective phi hphi

end SymmetricSubgroupAsymptotics.OrderNineAutomorphismDivisor
