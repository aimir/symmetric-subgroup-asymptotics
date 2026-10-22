import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveUnipotent
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylowCenterFamily
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneRootLine

/-! Arbitrary automorphisms of the ACTUAL central quotient preserve
its actual projected highest-root subgroup family. The proof acts on
the projected Sylow itself; no lift of an automorphism to the natural
matrix group or universal-cover identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootFamily
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexSylowCenterFamily CFSGOrthogonalDIndexPlaneRootLine
open CFSGOrthogonalDIndexProjectiveUnipotent
variable (K : Type) [Field K]

def projectiveHighestRootLine (s : ℕ) : Subgroup (elementaryProjective K (s + 4)) :=
  (highestRootLine K s).map (projection K s)

def projectiveConjugateRootLine (s : ℕ) (g : elementaryProjective K (s + 4)) :
    Subgroup (elementaryProjective K (s + 4)) :=
  (projectiveHighestRootLine K s).map (MulAut.conj g).toMonoidHom

theorem projectiveUnipotent_centerImage (s : ℕ) :
    centerImage (projectiveUnipotent K s) = projectiveHighestRootLine K s := by
  let e := unipotentProjectiveEquiv K s
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let u := e.symm z
    have hu : u ∈ Subgroup.center (unipotent K (s + 4)) :=
      ((Subgroup.centerCongr e).symm ⟨z, hz⟩).property
    refine ⟨u.val, ⟨u, hu, rfl⟩, ?_⟩
    have he := congrArg (fun t : projectiveUnipotent K s =>
      (t : elementaryProjective K (s + 4))) (e.apply_symm_apply z)
    exact he
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨e v, (Subgroup.centerCongr e ⟨v, hv⟩).property, rfl⟩

theorem automorphism_maps_projectiveConjugateRootLine [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4)))
    (g : elementaryProjective K (s + 4)) :
    ∃ h : elementaryProjective K (s + 4),
      (projectiveConjugateRootLine K s g).map f.toMonoidHom =
        projectiveConjugateRootLine K s h := by
  letI orthogonalDProjectiveRootFamilyFinite : Finite (elementaryProjective K (s + 4)) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center
      (elementaryRootGroup K (s + 4)))) (QuotientGroup.mk'_surjective _)
  obtain ⟨h, hh⟩ := exists_inner_centerImage_map p (projectiveSylow K s p)
    (f * MulAut.conj g)
  change (centerImage (projectiveUnipotent K s)).map (f * MulAut.conj g).toMonoidHom =
    (centerImage (projectiveUnipotent K s)).map (MulAut.conj h).toMonoidHom at hh
  rw [projectiveUnipotent_centerImage] at hh
  refine ⟨h, ?_⟩
  change ((projectiveHighestRootLine K s).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom = _
  rw [Subgroup.map_map]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootFamily
