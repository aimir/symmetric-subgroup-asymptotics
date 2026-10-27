import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveActualEquivalence

/-! Narrow original-pair generation for selected conjugacy orbit certificates.
The proof repeats the existing checked generation argument without importing
all twelve automorphism-incidence capacity modules. No simplicity is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveConjugacyOrbitGenerators
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveActualRepresentation

theorem original_pair_generates : Subgroup.closure ({x,y} : Set M12) = ⊤ := by
  let R := Subgroup.closure ({x,y} : Set M12)
  have htop : (⊤ : Subgroup CFSG.Models.Presentations.M12.Model) ≤
      R.comap representation := by
    rw [←PresentedGroup.closure_range_of {w | w ∈ CFSG.Models.Presentations.M12.relators}]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change representation (PresentedGroup.of (0 : Fin 2)) ∈ R
      rw [representation_of_zero]
      exact Subgroup.subset_closure (by simp)
    · change representation (PresentedGroup.of (1 : Fin 2)) ∈ R
      rw [representation_of_one]
      exact Subgroup.subset_closure (by simp)
  apply top_unique
  intro g _
  obtain ⟨z,rfl⟩ := CFSGMathieuTwelveActualEquivalence.representation_surjective g
  exact htop (by trivial)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveConjugacyOrbitGenerators
