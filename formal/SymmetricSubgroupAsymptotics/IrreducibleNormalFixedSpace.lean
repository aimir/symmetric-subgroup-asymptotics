import Mathlib.Tactic.Group
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation

/-! A faithful irreducible module has no invariants under a nontrivial
normal subgroup. This is elementary irreducibility, not a Clifford input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

private def normalFixedSubrepresentation (rho : Representation k G V)
    (L : Subgroup G) [L.Normal] : Subrepresentation rho where
  toSubmodule :=
    { carrier := {v | ∀ l : L,rho l.val v=v}
      zero_mem' := by intro l; exact map_zero _
      add_mem' := by intro v w hv hw l; rw [map_add,hv l,hw l]
      smul_mem' := by intro c v hv l; rw [map_smul,hv l] }
  apply_mem_toSubmodule := by
    intro g v hv l
    let l' : L := ⟨g⁻¹*l.val*g,
      by simpa only [inv_inv] using
        (inferInstance : L.Normal).conj_mem l.val l.property g⁻¹⟩
    calc
      rho l.val (rho g v)=rho g (rho l'.val v) := by
        have he : l.val*g=g*l'.val := by dsimp [l']; group
        change (rho l.val*rho g) v=(rho g*rho l'.val) v
        rw [←rho.map_mul,←rho.map_mul,he]
      _=rho g v := by rw [hv l']

 theorem irreducible_normal_fixed_eq_zero
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (hfaithful : Function.Injective rho)
    (L : Subgroup G) [L.Normal] (hL : L≠⊥)
    (v : V) (hv : ∀ l : L,rho l.val v=v) : v=0 := by
  let F := normalFixedSubrepresentation rho L
  have hnot : F≠⊤ := by
    intro ht
    apply hL
    apply le_antisymm ?_ bot_le
    intro l hl
    have he : rho l=1 := by
      apply LinearMap.ext
      intro w
      have hw : w∈F := by rw [ht]; exact Submodule.mem_top
      exact hw ⟨l,hl⟩
    exact Subgroup.mem_bot.mpr (hfaithful (he.trans rho.map_one.symm))
  have hb : F=⊥ := (eq_bot_or_eq_top F).resolve_right hnot
  have hmem : v∈F := hv
  rw [hb] at hmem
  exact hmem

end SymmetricSubgroupAsymptotics
