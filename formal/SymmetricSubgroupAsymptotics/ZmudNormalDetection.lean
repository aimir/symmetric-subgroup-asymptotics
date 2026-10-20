import SymmetricSubgroupAsymptotics.ZmudCoinducedEnvelopes
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group

/-! Elementary normal-subgroup detection: a nonzero scalar character on a
cyclic subgroup of N gives an N-fixed-free coinduced envelope. In an
irreducible representation, every ambient-normal subgroup acts trivially
or has zero fixed space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.ZmudNormalDetection

open ZmudFixedSpaceConstituents ZmudCoinducedEnvelopes

variable {G : Type} [Group G]

private def normalFixed
    {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (N : Subgroup G) [N.Normal] : Subrepresentation rho where
  toSubmodule := {
    carrier := {v | ∀ n : N, rho n.1 v = v}
    zero_mem' := by intro n; exact map_zero _
    add_mem' := by intro v w hv hw n; rw [map_add, hv n, hw n]
    smul_mem' := by intro c v hv n; rw [map_smul, hv n] }
  apply_mem_toSubmodule := by
    intro g v hv n
    let m : N := ⟨g⁻¹ * n.1 * g, by
      simpa only [inv_inv] using
        Subgroup.Normal.conj_mem inferInstance n.1 n.2 g⁻¹⟩
    have he : n.1 * g = g * m.1 := by dsimp only [m]; group
    calc
      rho n.1 (rho g v) = rho g (rho m.1 v) := by
        change (rho n.1 * rho g) v = (rho g * rho m.1) v
        rw [← map_mul, ← map_mul, he]
      _ = rho g v := by rw [hv m]

/-- The normal fixed-space dichotomy in the actual irreducible module. -/
theorem irreducible_dichotomy
    {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal] :
    (∀ (n : N) (v : V), rho n.1 v = v) ∨
      (∀ v : V, (∀ n : N, rho n.1 v = v) → v = 0) := by
  let F := normalFixed rho N
  rcases eq_bot_or_eq_top F with hbot | htop
  · right
    intro v hv
    have hm : v ∈ F := hv
    rw [hbot] at hm
    exact hm
  · left
    intro n v
    have hm : v ∈ F := by rw [htop]; trivial
    exact hm n

/-- The character only needs to live on a subgroup of N. N need not lie
inside the scalar inducing subgroup. -/
theorem scalarEnvelope_fixedFree_of_le
    [Finite G] (H N : Subgroup G) [N.Normal] (hHN : H ≤ N)
    (chi : H →* ℂ) (hchi : ∃ h : H, chi h ≠ 1)
    (f : (scalarEnvelope H chi).Space)
    (hf : ∀ n : N, (scalarEnvelope H chi).action n.1 f = f) : f = 0 := by
  obtain ⟨h, hh⟩ := hchi
  apply Subtype.ext
  funext g
  let n : N := ⟨g⁻¹ * h.1 * g, by
    simpa only [inv_inv] using
      Subgroup.Normal.conj_mem inferInstance h.1 (hHN h.2) g⁻¹⟩
  have he := congrArg (fun u : (scalarEnvelope H chi).Space => u.1 g) (hf n)
  change f.1 (g * (g⁻¹ * h.1 * g)) = f.1 g at he
  have hmul : g * (g⁻¹ * h.1 * g) = h.1 * g := by group
  rw [hmul] at he
  change f.1 (H.subtype h * g) = f.1 g at he
  rw [f.2 h g] at he
  change chi h * f.1 g = f.1 g at he
  have hz : (chi h - 1) * f.1 g = 0 := by
    rw [sub_mul, one_mul, he, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hh)

/-- Every nontrivial finite normal subgroup admits a nonzero finite
complex envelope with no fixed vectors for that subgroup. -/
theorem exists_envelope [Finite G] (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    ∃ E : Envelope G, ∀ v : E.Space, (∀ n : N, E.action n.1 v = v) → v = 0 := by
  obtain ⟨n, hn⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
  let H := Subgroup.zpowers n.1
  let a : H := ⟨n.1, Subgroup.mem_zpowers n.1⟩
  have ha : a ≠ 1 := fun he => hn (Subtype.ext (congrArg (fun z : H => (z : G)) he))
  letI : NeZero (Nat.card H) := ⟨(Nat.card_pos (α := H)).ne'⟩
  let e : Multiplicative (ZMod (Nat.card H)) ≃* H := zmodCyclicMulEquiv inferInstance
  let chi : H →* ℂ :=
    (ZMod.stdAddChar (N := Nat.card H)).toMonoidHom.comp e.symm.toMonoidHom
  have hchi : chi a ≠ 1 := by
    intro he
    have hz : (e.symm a).toAdd = 0 :=
      ZMod.injective_stdAddChar (he.trans ((ZMod.stdAddChar (N := Nat.card H)).map_zero_eq_one).symm)
    have he1 : e.symm a = 1 := Multiplicative.toAdd.injective hz
    exact ha (e.symm.injective (he1.trans (map_one e.symm).symm))
  have hHN : H ≤ N := (Subgroup.zpowers_le).mpr n.2
  exact ⟨scalarEnvelope H chi,
    scalarEnvelope_fixedFree_of_le H N hHN chi ⟨a, hchi⟩⟩

end SymmetricSubgroupAsymptotics.ZmudNormalDetection
