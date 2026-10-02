import SymmetricSubgroupAsymptotics.OrbitProfileProduct

/-!
# Internal profile coordinates act on the literal product group

An original profile symmetry permutes equal-action occurrences and changes
each local frame by an element of the corresponding normalizer.  This file
records the induced automorphism of the literal product of local actions.
It is the missing naturality bridge for upper-profile families which need
not be full on every coordinate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : Type*} {Ω : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}

@[simp] theorem orbitProfileCoordinatePerm_apply
    (a : OrbitProfileCoordinates Ω m U) (i : ι) (j : Fin (m i)) (x : Ω i) :
    orbitProfileCoordinatePerm a ⟨i,j,x⟩ =
      ⟨i, a.1 i j, (a.2 i j : Equiv.Perm (Ω i)) x⟩ := rfl

@[simp] theorem orbitProfileCoordinatePerm_symm_apply
    (a : OrbitProfileCoordinates Ω m U) (i : ι) (j : Fin (m i)) (x : Ω i) :
    (orbitProfileCoordinatePerm a).symm ⟨i,j,x⟩ =
      ⟨i, (a.1 i).symm j,
        (a.2 i ((a.1 i).symm j) : Equiv.Perm (Ω i)).symm x⟩ := rfl

/-- Conjugate local coordinates and reindex equal-action occurrences. -/
def orbitProfileProductCoordinateEquiv
    (a : OrbitProfileCoordinates Ω m U) :
    OrbitProfileProductGroup m U ≃* OrbitProfileProductGroup m U where
  toFun d i j :=
    let k := (a.1 i).symm j
    ⟨(a.2 i k : Equiv.Perm (Ω i)) * d i k *
        (a.2 i k : Equiv.Perm (Ω i))⁻¹,
      (Subgroup.mem_normalizer_iff.mp (a.2 i k).property (d i k)).mp
        (d i k).property⟩
  invFun d i j :=
    let k := a.1 i j
    ⟨(a.2 i j : Equiv.Perm (Ω i))⁻¹ * d i k *
        (a.2 i j : Equiv.Perm (Ω i)),
      (Subgroup.mem_normalizer_iff''.mp (a.2 i j).property (d i k)).mp
        (d i k).property⟩
  left_inv d := by
    funext i j
    apply Subtype.ext
    simp only [Equiv.symm_apply_apply]
    group
  right_inv d := by
    funext i j
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    group
  map_mul' d e := by
    funext i j
    apply Subtype.ext
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    group

/-- The induced product automorphism is literally conjugation of the block
permutation action by the corresponding internal coordinate permutation. -/
theorem orbitProfileProductCoordinateEquiv_action
    (a : OrbitProfileCoordinates Ω m U)
    (d : OrbitProfileProductGroup m U) :
    orbitProfileProductAction m U (orbitProfileProductCoordinateEquiv a d) =
      (orbitProfileCoordinatePerm a).permCongr
        (orbitProfileProductAction m U d) := by
  apply Equiv.ext
  rintro ⟨i,j,x⟩
  rw [Equiv.permCongr_apply, orbitProfileCoordinatePerm_symm_apply]
  change
    (⟨i,j,
      (((a.2 i ((a.1 i).symm j) : Equiv.Perm (Ω i)) *
          (d i ((a.1 i).symm j) : Equiv.Perm (Ω i)) *
          (a.2 i ((a.1 i).symm j) : Equiv.Perm (Ω i))⁻¹) x)⟩ :
        OrbitProfilePoints Ω m) =
      orbitProfileCoordinatePerm a
        ⟨i,(a.1 i).symm j,
          (d i ((a.1 i).symm j) : Equiv.Perm (Ω i))
            ((a.2 i ((a.1 i).symm j) : Equiv.Perm (Ω i)).symm x)⟩
  rw [orbitProfileCoordinatePerm_apply]
  simp only [Equiv.apply_symm_apply, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv]

/-- Conjugating a product-action subgroup by an internal profile symmetry
is the image of the same subgroup under the induced product automorphism. -/
theorem relabel_productAction_map_coordinate
    (a : OrbitProfileCoordinates Ω m U)
    (H : Subgroup (OrbitProfileProductGroup m U)) :
    relabelSubgroup (orbitProfileCoordinatePerm a)
        (H.map (orbitProfileProductAction m U)) =
      (H.map (orbitProfileProductCoordinateEquiv a).toMonoidHom).map
        (orbitProfileProductAction m U) := by
  change (H.map (orbitProfileProductAction m U)).map
      (orbitProfileCoordinatePerm a).permCongrHom.toMonoidHom = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro d
  exact (orbitProfileProductCoordinateEquiv_action a d).symm

end SymmetricSubgroupAsymptotics

end
