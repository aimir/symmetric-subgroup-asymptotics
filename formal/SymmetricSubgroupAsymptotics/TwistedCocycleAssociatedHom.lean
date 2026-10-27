import SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFrame
import Mathlib.Tactic.Group

/-! A literal cocycle for the actual conjugation action gives its actual
local homomorphism. The coordinate inclusion is retained, so equality of
local homomorphisms recovers the complete original cocycle. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.TwistedCocycleAssociatedHom
open TwistedMonomialCocycleFrame

variable {H A U : Type*} [Group H] [Group A] [Group U]
variable (α : H →* MulAut A) (β : H →* U) (ι : A →* U)
    (hcompat : ∀ h a,ι (α h a)=β h*ι a*(β h)⁻¹)

def associatedHom (c : Cocycle α) : H →* U where
  toFun h := ι (c.val h)*β h
  map_one' := by
    have hh : c.val 1=1 := by
      have he := c.property 1 1
      have he' : c.val 1*1=c.val 1*c.val 1 := by
        simpa only [one_mul,map_one,MulAut.one_apply,mul_one] using he
      exact (mul_left_cancel he').symm
    simp only [hh,map_one,mul_one]
  map_mul' p q := by
    change ι (c.val (p*q))*β (p*q)=
      (ι (c.val p)*β p)*(ι (c.val q)*β q)
    rw [c.property,map_mul,map_mul,hcompat]
    group

include hcompat in
theorem associatedHom_injective (hι : Function.Injective ι) :
    Function.Injective (associatedHom α β ι hcompat) := by
  intro c d h
  apply Subtype.ext
  funext a
  apply hι
  have hh := DFunLike.congr_fun h a
  change ι (c.val a)*β a=ι (d.val a)*β a at hh
  exact mul_right_cancel hh

end SymmetricSubgroupAsymptotics.TwistedCocycleAssociatedHom
