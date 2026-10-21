import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group
import Mathlib.Algebra.Field.ZMod

/-! A normal3-subgroup acts trivially on a finite irreducible ternary
module. Orbit congruence supplies a nonzero fixed vector; normality makes
the full fixed subspace invariant under the original ambient group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.IrreducibleTernaryNormalThreeGroup
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 3) V]
    (rho : Representation (ZMod 3) G V) (N : Subgroup G) [N.Normal]

def normalFixed : Subrepresentation rho where
  toSubmodule := {
    carrier := {v | ∀ n : N,rho n.val v=v}
    zero_mem' := by intro n; exact (rho n.val).map_zero
    add_mem' := by intro v w hv hw n; rw [map_add,hv n,hw n]
    smul_mem' := by intro a v hv n; rw [map_smul,hv n] }
  apply_mem_toSubmodule g v hv n := by
    let m : N := ⟨g⁻¹*n.val*g,by
      simpa only [inv_inv] using Subgroup.Normal.conj_mem (inferInstance : N.Normal)
        (n.val) n.property g⁻¹⟩
    have he : n.val*g=g*m.val := by dsimp only [m]; group
    change rho n.val (rho g v)=rho g v
    calc
      _=rho (n.val*g) v := by rw [map_mul]; rfl
      _=rho (g*m.val) v := by rw [he]
      _=rho g (rho m.val v) := by rw [map_mul]; rfl
      _=rho g v := by rw [hv m]

variable [Finite V]

theorem eq_bot_of_faithful_irreducible
    (hrho : Representation.IsIrreducible rho) (hfaithful : Function.Injective rho)
    (hN : IsPGroup 3 N) (hV : 3∣Nat.card V) : N=⊥ := by
  letI : MulAction N V := MulAction.compHom V
    (Representation.asGroupHom (rho.comp N.subtype))
  have hz : (0 : V)∈MulAction.fixedPoints N V := by
    intro n
    change rho n.val 0=0
    exact (rho n.val).map_zero
  obtain ⟨v,hv,hv0⟩ := hN.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hV hz
  have hvF : v∈normalFixed rho N := hv
  letI : Representation.IsIrreducible rho := hrho
  have htop : normalFixed rho N=⊤ := by
    rcases eq_bot_or_eq_top (normalFixed rho N) with hb|ht
    · have hvb : v∈(⊥ : Subrepresentation rho) := hb ▸ hvF
      have hvz : v=0 := hvb
      exact (hv0 hvz.symm).elim
    · exact ht
  apply le_antisymm _ bot_le
  intro n hn
  have he : rho n=rho 1 := by
    apply LinearMap.ext
    intro w
    have hw : w∈normalFixed rho N := by rw [htop]; trivial
    have hh := hw ⟨n,hn⟩
    simpa only [map_one,Module.End.one_apply] using hh
  exact hfaithful he

end SymmetricSubgroupAsymptotics.IrreducibleTernaryNormalThreeGroup
