import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtomFamilies
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.GroupTheory.Index

/-! The actual stabilizer of an inner-conjugacy family. Its index is
exactly the number of automorphism images of that same family. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
variable {G : Type*} [Group G]

theorem map_conj_automorphism (H : Subgroup G) (g : G) (f : MulAut G) :
    (H.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom =
      (H.map f.toMonoidHom).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  change f (g * y * g⁻¹) = f g * f y * (f g)⁻¹
  simp only [map_mul, map_inv]

theorem smul_innerFamily (f : MulAut G) (H : Subgroup G) :
    f • innerFamily H = innerFamily (H.map f.toMonoidHom) := by
  ext J
  constructor
  · rintro ⟨I, ⟨g, rfl⟩, rfl⟩
    exact ⟨f g, map_conj_automorphism H g f⟩
  · rintro ⟨g, rfl⟩
    refine ⟨H.map (MulAut.conj (f.symm g)).toMonoidHom, ⟨f.symm g, rfl⟩, ?_⟩
    change (H.map (MulAut.conj (f.symm g)).toMonoidHom).map f.toMonoidHom = _
    rw [map_conj_automorphism, f.apply_symm_apply]

def familyStabilizer (H : Subgroup G) : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) (innerFamily H)

theorem mem_familyStabilizer (H : Subgroup G) (f : MulAut G) :
    f ∈ familyStabilizer H ↔
      innerFamily (H.map f.toMonoidHom) = innerFamily H := by
  change f • innerFamily H = innerFamily H ↔ _
  rw [smul_innerFamily]

theorem orbit_innerFamily (H : Subgroup G) :
    MulAction.orbit (MulAut G) (innerFamily H) =
      Set.range (fun f : MulAut G => innerFamily (H.map f.toMonoidHom)) := by
  ext F
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (smul_innerFamily f H).symm.trans hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (smul_innerFamily f H).trans hf⟩

theorem familyStabilizer_index (H : Subgroup G) :
    (familyStabilizer H).index =
      Nat.card (Set.range (fun f : MulAut G => innerFamily (H.map f.toMonoidHom))) := by
  rw [familyStabilizer, MulAction.index_stabilizer, orbit_innerFamily,
    Nat.card_coe_set_eq]

theorem map_mem_innerFamily_of_stabilizer (H I : Subgroup G)
    (f : familyStabilizer H) (hI : I ∈ innerFamily H) :
    I.map f.val.toMonoidHom ∈ innerFamily H := by
  have hs : f.val • innerFamily H = innerFamily H := f.property
  rw [← hs]
  exact ⟨I, hI, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
