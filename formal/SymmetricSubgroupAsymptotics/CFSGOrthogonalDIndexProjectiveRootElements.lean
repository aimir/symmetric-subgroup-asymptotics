import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency

/-! The actual central quotient root-element set is intrinsically the
union of its defining-characteristic Sylow-centre root subgroups. Its
automorphism invariance is obtained inside the SAME quotient, without
lifting any automorphism to a natural matrix action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPairOperator
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexRootDisplacements
open CFSGOrthogonalDIndexProjectiveUnipotent CFSGOrthogonalDIndexProjectiveRootFamily
open CFSGOrthogonalDIndexProjectivePlaneLabel
variable (K : Type) [Field K]

theorem isProjectiveRootElement_iff_mem_rootLine (s : ℕ)
    (z : elementaryProjective K (s + 4)) :
    IsProjectiveRootElement K s z ↔
      ∃ g : elementaryProjective K (s + 4), z ∈ projectiveConjugateRootLine K s g := by
  constructor
  · rintro ⟨x, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨projection K s g, ?_⟩
    rw [← map_conjugateRootLine]
    refine ⟨g * highestRoot K s a * g⁻¹, ?_, rfl⟩
    exact (mem_conjugateRootLine_iff_exists s g _).mpr ⟨a, rfl⟩
  · rintro ⟨g, hz⟩
    have hsurj : Function.Surjective (projection K s) := QuotientGroup.mk'_surjective _
    obtain ⟨u, rfl⟩ := hsurj g
    rw [← map_conjugateRootLine] at hz
    obtain ⟨x, hx, he⟩ := hz
    obtain ⟨a, ha⟩ := (mem_conjugateRootLine_iff_exists s u x).mp hx
    exact ⟨x, ⟨u, a, ha⟩, he⟩

theorem automorphism_isProjectiveRootElement [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4)))
    (z : elementaryProjective K (s + 4)) (hz : IsProjectiveRootElement K s z) :
    IsProjectiveRootElement K s (f z) := by
  obtain ⟨g, hg⟩ := (isProjectiveRootElement_iff_mem_rootLine K s z).mp hz
  obtain ⟨h, hh⟩ := automorphism_maps_projectiveConjugateRootLine K p s f g
  have hm : f z ∈ (projectiveConjugateRootLine K s g).map f.toMonoidHom := ⟨z, hg, rfl⟩
  rw [hh] at hm
  exact (isProjectiveRootElement_iff_mem_rootLine K s (f z)).mpr ⟨h, hm⟩

theorem automorphism_isProjectiveRootElement_iff [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 4)))
    (z : elementaryProjective K (s + 4)) :
    IsProjectiveRootElement K s (f z) ↔ IsProjectiveRootElement K s z := by
  constructor
  · intro hz
    have h := automorphism_isProjectiveRootElement K p s f.symm (f z) hz
    simpa only [MulEquiv.symm_apply_apply] using h
  · exact automorphism_isProjectiveRootElement K p s f z

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexProjectiveRootAdjacency
