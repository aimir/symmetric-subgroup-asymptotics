import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A displayed finite-order element defines a computational homomorphism
from the additive residue group, with no chosen cyclic-group equivalence. -/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics
namespace ZModPowerHom

variable {G : Type} [Group G] (n : ℕ) [NeZero n] (g : G) (hg : g ^ n = 1)

def hom : Multiplicative (ZMod n) →* G where
  toFun c := g ^ c.toAdd.val
  map_one' := by
    change g ^ (0 : ZMod n).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' c d := by
    change g ^ (c.toAdd + d.toAdd).val = g ^ c.toAdd.val * g ^ d.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact pow_eq_pow_of_modEq (Nat.mod_modEq _ n) hg

theorem apply (c : Multiplicative (ZMod n)) : hom n g hg c = g ^ c.toAdd.val := rfl

theorem apply_ofAdd_one (hn : 1 < n) : hom n g hg (Multiplicative.ofAdd 1) = g := by
  change g ^ (1 : ZMod n).val = g
  rw [ZMod.val_one'' (ne_of_gt hn), pow_one]

end ZModPowerHom
end SymmetricSubgroupAsymptotics
