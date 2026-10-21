import Mathlib.RepresentationTheory.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel

/-! Actual orbit witnesses give a stabilizer bound without enumerating
the source. The injection uses actual products u_i*d in the original
group; no multiplication table or independent row group is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem subgroup_card_mul_le_of_linear_orbit_witnesses
    {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (R : Submodule k V)
    (hR : ∀ g : G, ∀ z ∈ R, rho g z ∈ R)
    (v : V) {m : ℕ} (u : Fin m → G)
    (hsep : ∀ i j : Fin m, i ≠ j → rho (u i) v - rho (u j) v ∉ R)
    (D : Subgroup G) (hfixed : ∀ d : D, rho (d : G) v - v ∈ R) :
    m * Nat.card D ≤ Nat.card G := by
  let f : Fin m × D → G := fun x => u x.1 * (x.2 : G)
  have hf : Function.Injective f := by
    rintro ⟨i,d⟩ ⟨j,e⟩ he
    change u i * (d : G) = u j * (e : G) at he
    have hd := hR (u i) _ (hfixed d)
    have hh := hR (u j) _ (hfixed e)
    rw [map_sub] at hd hh
    have heval := congrArg (fun g : G => rho g v) he
    change rho (u i * (d : G)) v = rho (u j * (e : G)) v at heval
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply] at heval
    rw [heval] at hd
    have hdiff : rho (u i) v - rho (u j) v ∈ R := by
      convert R.sub_mem hh hd using 1 <;> abel
    have hij : i = j := by
      by_contra hn
      exact hsep i j hn hdiff
    apply Prod.ext hij
    apply Subtype.ext
    exact mul_left_cancel (by simpa only [hij] using he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, Nat.card_fin] using hc

end SymmetricSubgroupAsymptotics
