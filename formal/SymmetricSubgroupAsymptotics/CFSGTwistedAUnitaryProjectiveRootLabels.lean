import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveUnipotentSeparation

/-! The conjugate central-root subgroups in the ORIGINAL unitary
projective model have exactly the proved natural point labels. Equality
descends and reflects through the actual cover by p-power separation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

private theorem subgroup_map_eq_iff_of_separation {G H : Type*} [Group G] [Group H]
    (f : G →* H) (P Q : Subgroup G)
    (hsep : ∀ x ∈ P, ∀ y ∈ Q, f x = f y → x = y) :
    P.map f = Q.map f ↔ P = Q := by
  constructor
  · intro he
    apply le_antisymm
    · intro x hx
      have hh : f x ∈ Q.map f := by rw [← he]; exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hh
      exact (hsep x hx y hy hyx.symm).symm ▸ hy
    · intro y hy
      have hh : f y ∈ P.map f := by rw [he]; exact ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hh
      exact hsep x hx y hy hxy ▸ hx
  · rintro rfl
    rfl

private theorem map_conjugate_subgroup {G H : Type*} [Group G] [Group H]
    (f : G →* H) (P : Subgroup G) (g : G) :
    (P.map f).map (MulAut.conj (f g)).toMonoidHom =
      (P.map (MulAut.conj g).toMonoidHom).map f := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change f g * f x * (f g)⁻¹ = f (g * x * g⁻¹)
  rw [map_mul, map_mul, map_inv]

def projectiveCentralRootLine (q : CFSG.PrimePower) (s : ℕ) :
    Subgroup (CFSG.Models.TwistedA (s + 3) q) :=
  (naturalCentralRootLine q (s + 1)).map (unitaryProjectiveCover q s)

def conjugateProjectiveCentralRootLine (q : CFSG.PrimePower) (s : ℕ)
    (g : CFSG.Models.TwistedA (s + 3) q) : Subgroup (CFSG.Models.TwistedA (s + 3) q) :=
  (projectiveCentralRootLine q s).map (MulAut.conj g).toMonoidHom

theorem conjugateProjectiveCentralRootLine_cover (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) :
    conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s g) =
      (conjugateNaturalCentralRootLine q (s + 1) g).map (unitaryProjectiveCover q s) := by
  change ((naturalCentralRootLine q (s + 1)).map (unitaryProjectiveCover q s)).map
      (MulAut.conj (unitaryProjectiveCover q s g)).toMonoidHom =
    ((naturalCentralRootLine q (s + 1)).map (MulAut.conj g).toMonoidHom).map
      (unitaryProjectiveCover q s)
  exact map_conjugate_subgroup (unitaryProjectiveCover q s) (naturalCentralRootLine q (s + 1)) g

theorem conjugateProjectiveCentralRootLine_eq_iff_point_eq (q : CFSG.PrimePower) (s : ℕ)
    (g h : naturalFixed (s + 3) q) :
    conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s g) =
        conjugateProjectiveCentralRootLine q s (unitaryProjectiveCover q s h) ↔
      conjugateCentralPoint q (s + 1) g = conjugateCentralPoint q (s + 1) h := by
  rw [conjugateProjectiveCentralRootLine_cover, conjugateProjectiveCentralRootLine_cover,
    subgroup_map_eq_iff_of_separation (unitaryProjectiveCover q s)
      (conjugateNaturalCentralRootLine q (s + 1) g)
      (conjugateNaturalCentralRootLine q (s + 1) h) (by
        intro x hx y hy he
        exact unitaryProjectiveCover_eq_of_p_powers q s x y
          (conjugateNaturalCentralRootLine_p_power q s g x hx)
          (conjugateNaturalCentralRootLine_p_power q s h y hy) he)]
  exact conjugateNaturalCentralRootLine_eq_iff_point_eq q (s + 1) g h

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
