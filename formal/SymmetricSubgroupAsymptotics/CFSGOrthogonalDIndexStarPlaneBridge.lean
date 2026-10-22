import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexStarVectorBridge
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticStarPairs
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexR11Action
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion

/-! The exact local star-bridge axiom on the ORIGINAL quadratic
singular two-planes, in every characteristic. Its extra not-both-R11
premise is used to obtain the quadratic-shell vector; it is not dropped
in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexQuadraticCorrection
open CFSGOrthogonalDIndexQuadraticStarPairs CFSGOrthogonalDIndexStarVectorBridge
open CFSGTwoDimensionalSubmoduleBasis CFSGPolarCommonPointPlanes
variable (K : Type) [Field K]

theorem exists_star_bridge (s : ℕ) (u : Index (s + 5) → K) (hu : u ≠ 0)
    (P Q T : SingularPlanes K (s + 1))
    (huP : u ∈ P.val) (huQ : u ∈ Q.val) (huT : u ∈ T.val)
    (hPQ : IntersectingNonadjacent K (s + 1) P Q)
    (havoid : ¬(IntersectingNonadjacent K (s + 1) P T ∧
      IntersectingNonadjacent K (s + 1) Q T)) :
    ∃ R : SingularPlanes K (s + 1), u ∈ R.val ∧
      IntersectingNonadjacent K (s + 1) P R ∧
      IntersectingNonadjacent K (s + 1) Q R ∧
      IntersectingNonadjacent K (s + 1) T R := by
  let A := splitQuadraticForm K (s + 5)
  obtain ⟨v, hv, hnv, hspanP⟩ := exists_companion P.val P.property.1 u huP hu
  obtain ⟨w, hw, hnw, hspanQ⟩ := exists_companion Q.val Q.property.1 u huQ hu
  obtain ⟨t, ht, hnt, hspanT⟩ := exists_companion T.val T.property.1 u huT hu
  have hQu : A u = 0 := P.property.2 u huP
  have hQv : A v = 0 := P.property.2 v hv
  have hQw : A w = 0 := Q.property.2 w hw
  have hQt : A t = 0 := T.property.2 t ht
  have huv : A.polarBilin u v = 0 := polar_zero_of_singular A P.val P.property.2 u v huP hv
  have huw : A.polarBilin u w = 0 := polar_zero_of_singular A Q.val Q.property.2 u w huQ hw
  have hut : A.polarBilin u t = 0 := polar_zero_of_singular A T.val T.property.2 u t huT ht
  have hvw : A.polarBilin v w ≠ 0 := by
    apply pairing_ne_zero_of_nonsingular_join A u v w hQu hQv hQw huv huw
    simpa only [hspanP, hspanQ] using hPQ.2
  have hav : A.polarBilin v t = 0 ∨ A.polarBilin w t = 0 := by
    by_cases hvt : A.polarBilin v t = 0
    · exact Or.inl hvt
    · right
      by_contra hwt
      apply havoid
      exact ⟨intersecting_nonsingular_of_pairing A P.val T.val P.property.1 T.property.1
        P.property.2 T.property.2 u v t hu huP huT hv ht hvt,
        intersecting_nonsingular_of_pairing A Q.val T.val Q.property.1 T.property.1
          Q.property.2 T.property.2 u w t hu huQ huT hw ht hwt⟩
  obtain ⟨d, hdQ, hud, hvd, hwd, htd⟩ := exists_star_vector K s u v w t hu hnv hnt
    hQu hQv hQw hQt huv huw hut hvw hav
  have hnd : ∀ c : K, d ≠ c • u := by
    intro c he
    apply hvd
    have hvu : A.polarBilin v u = 0 :=
      polar_zero_of_singular A P.val P.property.2 v u hv huP
    dsimp only [A] at hvu
    simp only [he, map_smul, hvu, smul_zero]
  let R : SingularPlanes K (s + 1) := ⟨Submodule.span K {u, d},
    pairPlane_finrank u d hu hnd, singular_span_pair A u d hQu hdQ hud⟩
  have huR : u ∈ R.val := Submodule.subset_span (Or.inl rfl)
  have hdR : d ∈ R.val := Submodule.subset_span (Or.inr rfl)
  exact ⟨R, huR,
    intersecting_nonsingular_of_pairing A P.val R.val P.property.1 R.property.1
      P.property.2 R.property.2 u v d hu huP huR hv hdR hvd,
    intersecting_nonsingular_of_pairing A Q.val R.val Q.property.1 R.property.1
      Q.property.2 R.property.2 u w d hu huQ huR hw hdR hwd,
    intersecting_nonsingular_of_pairing A T.val R.val T.property.1 R.property.1
      T.property.2 R.property.2 u t d hu huT huR ht hdR htd⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneFamilyAction
