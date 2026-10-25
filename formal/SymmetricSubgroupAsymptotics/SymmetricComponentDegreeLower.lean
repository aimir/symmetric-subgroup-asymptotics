import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Perm
import Lean.Elab.Tactic.Omega

/-! An actual faithful permutation component abstractly isomorphic to
S_m has degree at least m. Only its original subgroup inclusion is used;
its permutation representation need not be the natural one. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SymmetricComponentDegreeLower

theorem degree_le {Y : Type*} [Finite Y]
    (C : Subgroup (Equiv.Perm Y)) (m : ℕ) (hm : 2 ≤ m)
    (e : C ≃* Equiv.Perm (Fin m)) : m ≤ Nat.card Y := by
  have hfac : m.factorial ≤ (Nat.card Y).factorial := by
    have hh := Nat.card_le_card_of_injective C.subtype Subtype.val_injective
    rwa [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin, Nat.card_perm] at hh
  have ha : 1 < Nat.card Y := Nat.one_lt_factorial.mp
    ((Nat.one_lt_factorial.mpr (by omega : 1 < m)).trans_le hfac)
  by_contra hle
  have hlt : (Nat.card Y).factorial < m.factorial :=
    Nat.factorial_lt_of_lt (by omega) (by omega)
  omega

end SymmetricSubgroupAsymptotics.SymmetricComponentDegreeLower
