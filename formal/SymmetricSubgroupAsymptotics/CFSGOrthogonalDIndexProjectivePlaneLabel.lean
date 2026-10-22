import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootLift
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootFamily

/-! Equal actual projective root subgroups have exactly the same
original natural two-plane label. The proof uses uniqueness of actual
rank-two root representatives; no lift of an abstract automorphism is
assumed and no rank-four triality statement is built into the label. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectivePlaneLabel
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootPlaneImage
open CFSGOrthogonalDIndexProjectiveUnipotent CFSGOrthogonalDIndexProjectiveRootFamily
open CFSGOrthogonalDIndexProjectiveRootLift
variable (K : Type) [Field K]

theorem map_conjugateRootLine (s : ℕ) (g : elementaryRootGroup K (s + 4)) :
    (conjugateRootLine K s g).map (projection K s) =
      projectiveConjugateRootLine K s (projection K s g) := by
  change ((highestRootLine K s).map (MulAut.conj g).toMonoidHom).map (projection K s) =
    ((highestRootLine K s).map (projection K s)).map
      (MulAut.conj (projection K s g)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem mem_conjugateRootLine_iff (s : ℕ) (g x : elementaryRootGroup K (s + 4)) :
    x ∈ conjugateRootLine K s g ↔ ∃ a : K, x = g * highestRoot K s a * g⁻¹ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_highestRootLine_iff K s u).mp hu
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨highestRoot K s a, (mem_highestRootLine_iff K s _).mpr ⟨a, rfl⟩, rfl⟩

private theorem conjugateRootLine_le_of_projective_map_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (he : (conjugateRootLine K s g).map (projection K s) =
      (conjugateRootLine K s h).map (projection K s)) :
    conjugateRootLine K s g ≤ conjugateRootLine K s h := by
  intro x hx
  have hm : projection K s x ∈ (conjugateRootLine K s g).map (projection K s) :=
    ⟨x, hx, rfl⟩
  rw [he] at hm
  obtain ⟨y, hy, hxy⟩ := hm
  obtain ⟨a, ha⟩ := (mem_conjugateRootLine_iff K s g x).mp hx
  obtain ⟨b, hb⟩ := (mem_conjugateRootLine_iff K s h y).mp hy
  have hu : g * highestRoot K s a * g⁻¹ = h * highestRoot K s b * h⁻¹ :=
    conjugate_highestRoot_eq_of_projective_eq K s g h a b (by
      rw [← ha, ← hb]
      exact hxy.symm)
  have hsame : x = y := ha.trans (hu.trans hb.symm)
  exact hsame.symm ▸ hy

theorem conjugateRootLine_eq_of_projective_map_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4))
    (he : (conjugateRootLine K s g).map (projection K s) =
      (conjugateRootLine K s h).map (projection K s)) :
    conjugateRootLine K s g = conjugateRootLine K s h :=
  le_antisymm (conjugateRootLine_le_of_projective_map_eq K s g h he)
    (conjugateRootLine_le_of_projective_map_eq K s h g he.symm)

theorem projectiveConjugateRootLine_eq_iff_plane_eq (s : ℕ)
    (g h : elementaryRootGroup K (s + 4)) :
    projectiveConjugateRootLine K s (projection K s g) =
        projectiveConjugateRootLine K s (projection K s h) ↔
      conjugateRootPlane K s g = conjugateRootPlane K s h := by
  constructor
  · intro he
    rw [← map_conjugateRootLine, ← map_conjugateRootLine] at he
    exact (conjugateRootLine_eq_iff_plane_eq K s g h).mp
      (conjugateRootLine_eq_of_projective_map_eq K s g h he)
  · intro hp
    rw [← map_conjugateRootLine, ← map_conjugateRootLine,
      (conjugateRootLine_eq_iff_plane_eq K s g h).mpr hp]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectivePlaneLabel
