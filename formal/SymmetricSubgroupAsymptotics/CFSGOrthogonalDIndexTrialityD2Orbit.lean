import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace

/-! Every literal maximal Q-singular residual D2 plane is taken by
an ACTUAL original elementary word to one of the two standard directions.
This is proved from the coordinate normalizer of a singular vector and
the actual quadratic equation, not an identification with a named group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexAllRankQuadraticForm
open CFSGOrthogonalDIndexVectorCoordinates CFSGOrthogonalDIndexPositiveSpace
variable (K : Type) [Field K]

theorem exists_elementary_plane_normal_form (P : Submodule K (Index 2 → K))
    (hP : Module.finrank K P = 2) (hPs : ∀ x ∈ P, splitQuadraticForm K 2 x = 0) :
    ∃ g : elementaryRootGroup K 2,
      P.map (naturalLinearHom K 2 g).toLinearMap = positivePlane K ∨
      P.map (naturalLinearHom K 2 g).toLinearMap = crossingPlane K := by
  have hne : P ≠ ⊥ := by
    intro he
    have hh := congrArg (fun W : Submodule K (Index 2 → K) => Module.finrank K W) he
    change Module.finrank K P = Module.finrank K (⊥ : Submodule K (Index 2 → K)) at hh
    rw [hP, finrank_bot] at hh
    omega
  obtain ⟨u, huP, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨g, hgu⟩ := exists_normalize_singular K 0 u hu
    ((splitQuadraticForm_apply K 2 u).symm.trans (hPs u huP))
  let e := naturalLinearHom K 2 g
  have heQ (x : Index 2 → K) : splitQuadraticForm K 2 (e x) = splitQuadraticForm K 2 x := by
    rw [splitQuadraticForm_apply, splitQuadraticForm_apply]
    exact elementary_preserves_splitQ_all_ranks K 2 (by decide) g x
  have he0 : e0 K ∈ P.map e.toLinearMap := by
    refine ⟨u, huP, ?_⟩
    exact hgu
  have hdim : Module.finrank K (P.map e.toLinearMap) = 2 := (e.finrank_map_eq P).trans hP
  have hsing : ∀ x ∈ P.map e.toLinearMap, splitQuadraticForm K 2 x = 0 := by
    rintro x ⟨y, hy, rfl⟩
    exact (heQ y).trans (hPs y hy)
  exact ⟨g, singular_plane_through_e0 K (P.map e.toLinearMap) hdim hsing he0⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
