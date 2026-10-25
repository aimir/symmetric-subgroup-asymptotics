import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Literal intersection transport under a group action by automorphisms.
Two subgroup-preserving outside factors can be stripped from a three-factor
word. The action can be ambient conjugation on a normal subgroup; no acting
element is thereby asserted to belong to that normal subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport
variable {G H : Type*} [Group G] [Group H]

theorem mem_intersection_of_map_eq (P : Subgroup H) (f : H →* H) (x : H)
    (hx : x ∈ P) (he : f x = x) : x ∈ P ⊓ P.comap f := by
  refine ⟨hx, ?_⟩
  change f x ∈ P
  exact he.symm ▸ hx

theorem comap_intersection_mul (rho : G →* MulAut H) (P : Subgroup H) (u w v : G)
    (hu : ∀ x : H, rho u x ∈ P ↔ x ∈ P)
    (hv : ∀ x : H, rho v x ∈ P ↔ x ∈ P) :
    P ⊓ P.comap (rho (u*w*v)).toMonoidHom =
      (P ⊓ P.comap (rho w).toMonoidHom).comap (rho v).toMonoidHom := by
  ext x
  change (x ∈ P ∧ rho (u*w*v) x ∈ P) ↔
    (rho v x ∈ P ∧ rho w (rho v x) ∈ P)
  rw [map_mul, map_mul]
  change (x ∈ P ∧ rho u (rho w (rho v x)) ∈ P) ↔
    (rho v x ∈ P ∧ rho w (rho v x) ∈ P)
  rw [hu (rho w (rho v x)), hv x]

theorem comap_intersection_mul_eq_bot_iff
    (rho : G →* MulAut H) (P : Subgroup H) (u w v : G)
    (hu : ∀ x : H, rho u x ∈ P ↔ x ∈ P)
    (hv : ∀ x : H, rho v x ∈ P ↔ x ∈ P) :
    P ⊓ P.comap (rho (u*w*v)).toMonoidHom = ⊥ ↔
      P ⊓ P.comap (rho w).toMonoidHom = ⊥ := by
  rw [comap_intersection_mul rho P u w v hu hv]
  have hb : (⊥ : Subgroup H).comap (rho v).toMonoidHom = ⊥ :=
    (MonoidHom.comap_bot _).trans ((rho v).toMonoidHom.ker_eq_bot_iff.mpr (rho v).injective)
  constructor
  · intro h
    apply Subgroup.comap_injective (f := (rho v).toMonoidHom) (rho v).surjective
    exact h.trans hb.symm
  · intro h
    rw [h]
    exact hb

theorem map_eq_comap_inverse (rho : G →* MulAut H) (P : Subgroup H) (g : G) :
    P.map (rho g).toMonoidHom = P.comap (rho (g⁻¹)).toMonoidHom := by
  have hi : rho (g⁻¹) = (rho g).symm := map_inv rho g
  rw [hi]
  exact Subgroup.map_equiv_eq_comap_symm' (rho g) P

theorem normal_comap_conjugate (N P : Subgroup G) [N.Normal] (g : G) :
    (P.map (MulAut.conj g).toMonoidHom).comap N.subtype =
      (P.comap N.subtype).map (MulAut.conjNormal g).toMonoidHom := by
  rw [map_eq_comap_inverse (MulAut.conj) P g,
    map_eq_comap_inverse (MulAut.conjNormal) (P.comap N.subtype) g]
  ext x
  rfl

theorem normal_comap_invariant (N P : Subgroup G) [N.Normal]
    (u : G) (hu : u ∈ P) (x : N) :
    MulAut.conjNormal u x ∈ P.comap N.subtype ↔ x ∈ P.comap N.subtype := by
  change u*(x : G)*u⁻¹ ∈ P ↔ (x : G) ∈ P
  exact ((P.le_normalizer hu) (x : G)).symm

end SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport
