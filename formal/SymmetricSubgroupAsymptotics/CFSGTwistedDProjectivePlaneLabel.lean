import SymmetricSubgroupAsymptotics.CFSGTwistedDRootPlaneImage
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootLift

/-! Exact fixed-field two-plane labels for the SAME projective relative
root family. Ambient scalar uniqueness removes only a possible central
scalar between two actual relative roots; all plane labels remain over
the fixed field. No arbitrary quotient automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDProjectivePlaneLabel
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeUnipotentSylow CFSGTwistedDRelativeProjectiveModel
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDProjectiveRootFamily
open CFSGTwistedDPlaneRootLine CFSGTwistedDRootPlaneImage
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedA2FixedField

theorem center_maps_center (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup.center (relativeRootGroup (s + 2) q) ≤
      (Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4))).comap
        (relativeInclusion s q) := by
  intro x hx
  exact (centerInclusion s q ⟨x, hx⟩).property

def projectiveAmbientHom (s : ℕ) (q : CFSG.PrimePower) :
    Projective s q →* elementaryProjective (q.Extension 2) (s + 4) :=
  QuotientGroup.map (Subgroup.center (relativeRootGroup (s + 2) q))
    (Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)))
    (relativeInclusion s q) (center_maps_center s q)

theorem projectiveAmbientHom_apply (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) :
    projectiveAmbientHom s q (projection s q g) =
      CFSGOrthogonalDIndexProjectiveUnipotent.projection (q.Extension 2) s
        (relativeInclusion s q g) := rfl

theorem inclusion_conjugate_highest (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) (a : fixedField q) :
    relativeInclusion s q (g * highestRoot s q a * g⁻¹) =
      relativeInclusion s q g *
        CFSGOrthogonalDIndexPairOperator.highestRoot (q.Extension 2) s (a : q.Extension 2) *
          (relativeInclusion s q g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  rfl

theorem conjugate_highest_eq_of_projective_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q) (a b : fixedField q)
    (he : projection s q (g * highestRoot s q a * g⁻¹) =
      projection s q (h * highestRoot s q b * h⁻¹)) :
    g * highestRoot s q a * g⁻¹ = h * highestRoot s q b * h⁻¹ := by
  have heA := congrArg (projectiveAmbientHom s q) he
  rw [projectiveAmbientHom_apply, projectiveAmbientHom_apply,
    inclusion_conjugate_highest, inclusion_conjugate_highest] at heA
  apply relativeInclusion_injective s q
  rw [inclusion_conjugate_highest, inclusion_conjugate_highest]
  exact CFSGOrthogonalDIndexProjectiveRootLift.conjugate_highestRoot_eq_of_projective_eq
    (q.Extension 2) s (relativeInclusion s q g) (relativeInclusion s q h)
    (a : q.Extension 2) (b : q.Extension 2) heA

theorem map_conjugateRootLine (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) :
    (conjugateRootLine s q g).map (projection s q) =
      projectiveConjugateRootLine s q (projection s q g) := by
  change ((highestRootLine s q).map (MulAut.conj g).toMonoidHom).map (projection s q) =
    ((highestRootLine s q).map (projection s q)).map
      (MulAut.conj (projection s q g)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem conjugateRootLine_le_of_projective_map_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (he : (conjugateRootLine s q g).map (projection s q) =
      (conjugateRootLine s q h).map (projection s q)) :
    conjugateRootLine s q g ≤ conjugateRootLine s q h := by
  intro x hx
  have hm : projection s q x ∈ (conjugateRootLine s q g).map (projection s q) :=
    ⟨x, hx, rfl⟩
  rw [he] at hm
  obtain ⟨y, hy, hxy⟩ := hm
  obtain ⟨a, ha⟩ := (mem_conjugateRootLine_iff s q g x).mp hx
  obtain ⟨b, hb⟩ := (mem_conjugateRootLine_iff s q h y).mp hy
  have hu := conjugate_highest_eq_of_projective_eq s q g h a b (by
    rw [← ha, ← hb]
    exact hxy.symm)
  have hsame : x = y := ha.trans (hu.trans hb.symm)
  exact hsame.symm ▸ hy

theorem conjugateRootLine_eq_of_projective_map_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (he : (conjugateRootLine s q g).map (projection s q) =
      (conjugateRootLine s q h).map (projection s q)) :
    conjugateRootLine s q g = conjugateRootLine s q h :=
  le_antisymm (conjugateRootLine_le_of_projective_map_eq s q g h he)
    (conjugateRootLine_le_of_projective_map_eq s q h g he.symm)

theorem projectiveConjugateRootLine_eq_iff_plane_eq (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q) :
    projectiveConjugateRootLine s q (projection s q g) =
        projectiveConjugateRootLine s q (projection s q h) ↔
      conjugateRootPlane s q g = conjugateRootPlane s q h := by
  constructor
  · intro he
    rw [← map_conjugateRootLine, ← map_conjugateRootLine] at he
    exact (conjugateRootLine_eq_iff_plane_eq s q g h).mp
      (conjugateRootLine_eq_of_projective_map_eq s q g h he)
  · intro hp
    rw [← map_conjugateRootLine, ← map_conjugateRootLine,
      (conjugateRootLine_eq_iff_plane_eq s q g h).mpr hp]

end SymmetricSubgroupAsymptotics.CFSGTwistedDProjectivePlaneLabel
