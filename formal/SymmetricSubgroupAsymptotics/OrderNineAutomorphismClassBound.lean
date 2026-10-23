import SymmetricSubgroupAsymptotics.FiniteLinearPlaneFixedSpace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! The actual automorphisms of every noncyclic abelian group of order
nine act faithfully on its original additive F3 plane. Both the class
budget and the nonidentity fixed-space budget are derived internally.
There is no primitive-action or supplied linear-recognition premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OrderNineAutomorphismClassBound
open FiniteLinearPlaneClassBound

local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩
variable {N H : Type*} [CommGroup N] [Group H]

private def ternaryModule (hN : Nat.card N = 9) (hnc : ¬ IsCyclic N) :
    Module Scalar (Additive N) :=
  AddCommGroup.zmodModule (n := 3) (fun x => by
    apply Additive.toMul.injective
    change x.toMul^3=1
    have hexp : Monoid.exponent N=3 :=
      (not_isCyclic_iff_exponent_eq_prime (by decide : Nat.Prime 3)
        (by simpa only [show (3 : ℕ)^2=9 by decide] using hN)).mp hnc
    simpa only [hexp] using Monoid.pow_exponent_eq_one x.toMul)

def automorphismLinear [Module Scalar (Additive N)] :
    MulAut N →* (Additive N ≃ₗ[Scalar] Additive N) where
  toFun a := { a.toAdditive with map_smul' := fun c x => ZMod.map_smul a.toAdditive c x }
  map_one' := by ext x; rfl
  map_mul' _a _b := by ext x; rfl

theorem automorphismLinear_injective [Module Scalar (Additive N)] :
    Function.Injective (automorphismLinear (N := N)) := by
  intro a b he
  apply MulEquiv.ext
  intro x
  exact congrArg Additive.toMul (DFunLike.congr_fun he (Additive.ofMul x))

theorem class_card_le_ten [Finite N] [Finite H]
    (hN : Nat.card N = 9) (hnc : ¬ IsCyclic N)
    (φ : H →* MulAut N) (hφ : Function.Injective φ) :
    Nat.card (ConjClasses H) ≤ 10 := by
  letI : Module Scalar (Additive N) := ternaryModule hN hnc
  let ρ : H →* (Additive N ≃ₗ[Scalar] Additive N) := automorphismLinear.comp φ
  have hρ : Function.Injective ρ := automorphismLinear_injective.comp hφ
  have hA : Nat.card (Additive N)=9 := hN
  exact FiniteLinearPlaneClassBound.class_card_le_ten ρ hA hρ

theorem fixed_card_le_three [Finite N]
    (hN : Nat.card N = 9) (hnc : ¬ IsCyclic N)
    (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (h : H) (hh : h ≠ 1) : Nat.card {n : N // φ h n=n} ≤ 3 := by
  letI : Module Scalar (Additive N) := ternaryModule hN hnc
  let ρ : H →* (Additive N ≃ₗ[Scalar] Additive N) := automorphismLinear.comp φ
  have hρ : Function.Injective ρ := automorphismLinear_injective.comp hφ
  have he : ρ h ≠ 1 := fun he => hh (hρ (he.trans ρ.map_one.symm))
  have hA : Nat.card (Additive N)=9 := hN
  let e : {n : N // φ h n=n} ≃ {v : Additive N // ρ h v=v} := {
    toFun := fun n => ⟨Additive.ofMul n.val, congrArg Additive.ofMul n.property⟩
    invFun := fun v => ⟨v.val.toMul, congrArg Additive.toMul v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans_le (FiniteLinearPlaneFixedSpace.fixed_card_le_three hA (ρ h) he)

end SymmetricSubgroupAsymptotics.OrderNineAutomorphismClassBound
