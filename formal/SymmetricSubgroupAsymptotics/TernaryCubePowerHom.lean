import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Group.TypeTags.Hom

/-! The actual cyclic homomorphism supplied by a cube-one group element.
The construction factors integer powers through ZMod, rather than
assuming a coordinate map or performing a finite group enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.TernaryCubePowerHom
variable {G : Type*} [Group G]

private def integerPowers (x : G) : ℤ →+ Additive G where
  toFun n := Additive.ofMul (x^n)
  map_zero' := by change x^(0:ℤ)=1; exact zpow_zero x
  map_add' m n := by change x^(m+n)=x^m*x^n; exact zpow_add x m n

def powerHom (x : G) (hx : x^3=1) : Multiplicative (ZMod 3) →* G :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift 3
    ⟨integerPowers x,by change x^(3:ℤ)=1; exact (zpow_natCast x 3).trans hx⟩)

theorem powerHom_natCast (x : G) (hx : x^3=1) (n : ℕ) :
    powerHom x hx (Multiplicative.ofAdd (n : ZMod 3))=x^n := by
  change (ZMod.lift 3
    ⟨integerPowers x,by change x^(3:ℤ)=1; exact (zpow_natCast x 3).trans hx⟩
      (n : ZMod 3)).toMul=x^n
  have h := ZMod.lift_coe 3
    (⟨integerPowers x,by change x^(3:ℤ)=1; exact (zpow_natCast x 3).trans hx⟩)
    (n : ℤ)
  have hh := congrArg Additive.toMul h
  change (ZMod.lift 3
    ⟨integerPowers x,by change x^(3:ℤ)=1; exact (zpow_natCast x 3).trans hx⟩
      ((n : ℤ) : ZMod 3)).toMul=x^(n : ℤ) at hh
  simpa only [Int.cast_natCast,zpow_natCast] using hh

theorem powerHom_val (x : G) (hx : x^3=1) (c : ZMod 3) :
    powerHom x hx (Multiplicative.ofAdd c)=x^c.val := by
  simpa only [ZMod.natCast_zmod_val] using powerHom_natCast x hx c.val

theorem powerHom_one (x : G) (hx : x^3=1) :
    powerHom x hx (Multiplicative.ofAdd (1 : ZMod 3))=x := by
  simpa only [Nat.cast_one,pow_one] using powerHom_natCast x hx 1

theorem powerHom_injective (x : G) (hx : x^3=1) (hne : x≠1) :
    Function.Injective (powerHom x hx) := by
  have ho : orderOf x=3 := by
    have hd := orderOf_dvd_of_pow_eq_one hx
    have hn : orderOf x≠1 := fun he => hne (orderOf_eq_one_iff.mp he)
    exact ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd).resolve_left hn
  apply (powerHom x hx).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro c hc
  change c=1
  have hp : x^c.toAdd.val=1 := by
    rw [←powerHom_val x hx c.toAdd]
    exact hc
  have hd : orderOf x∣c.toAdd.val := orderOf_dvd_of_pow_eq_one hp
  rw [ho] at hd
  have hlt := ZMod.val_lt c.toAdd
  rcases hd with ⟨m,hm⟩
  have hv : c.toAdd.val=0 := by omega
  apply Multiplicative.toAdd.injective
  apply ZMod.val_injective 3
  change c.toAdd.val=(0 : ZMod 3).val
  simpa only [ZMod.val_zero] using hv

end SymmetricSubgroupAsymptotics.TernaryCubePowerHom
