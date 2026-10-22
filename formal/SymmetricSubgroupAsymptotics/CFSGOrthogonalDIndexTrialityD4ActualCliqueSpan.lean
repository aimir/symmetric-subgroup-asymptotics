import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CliqueSpan
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4RootedCliqueGeometry

/-! The actual global plane sets recover the containing three-space
or maximal singular four-space. In particular their natural geometric
types cannot coincide by a loss of their original q-element fibres. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4CliqueSpan
variable (K : Type) [Field K]

def originalCliqueSpan (T : Set (SingularPlanes K 0)) : Submodule K (Index 4 → K) :=
  sSup {P | ∃ S ∈ T, S.val = P}

theorem literal_top_span (W : ThreeExtensions K) :
    originalCliqueSpan K {P : SingularPlanes K 0 | P.val ≤ W.val} = W.val := by
  have hset : {P : Submodule K (Index 4 → K) |
      ∃ S ∈ {S : SingularPlanes K 0 | S.val ≤ W.val}, S.val = P} =
      {P : Submodule K (Index 4 → K) | Module.finrank K P = 2 ∧ P ≤ W.val} := by
    ext P
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S.property.1, hS⟩
    · intro hP
      refine ⟨⟨P, hP.1, fun x hx => W.property.2.1 x (hP.2 hx)⟩, hP.2, rfl⟩
  unfold originalCliqueSpan
  rw [hset]
  exact two_planes_span_space W.val (by rw [W.property.1]; decide)

theorem literal_star_span (U : RootPoints K) (M : MaximalExtensions K) :
    originalCliqueSpan K {P : SingularPlanes K 0 | U.val ≤ P.val ∧ P.val ≤ M.val} = M.val := by
  have hset : {P : Submodule K (Index 4 → K) |
      ∃ S ∈ {S : SingularPlanes K 0 | U.val ≤ S.val ∧ S.val ≤ M.val}, S.val = P} =
      {P : Submodule K (Index 4 → K) | Module.finrank K P = 2 ∧ U.val ≤ P ∧ P ≤ M.val} := by
    ext P
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S.property.1, hS⟩
    · intro hP
      refine ⟨⟨P, hP.1, fun x hx => M.property.2.1 x (hP.2.2 hx)⟩, hP.2, rfl⟩
  unfold originalCliqueSpan
  rw [hset]
  exact star_planes_span_space U.val M.val U.property.1
    (U.property.2.trans M.property.2.2) (by rw [M.property.1]; decide)

theorem completed_top_span (W : ThreeExtensions K) :
    originalCliqueSpan K (rootCompletedClique K (neighborTop K W)) = W.val := by
  rw [rootCompleted_top_eq]
  exact literal_top_span K W

theorem completed_columnStar_span (U : RootPoints K)
    (p : CFSGOrthogonalDIndexTrialityD2Coordinates.RulingParameters K) :
    originalCliqueSpan K (rootCompletedClique K (neighborColumnStar K U p)) =
      (columnMaximalExtension K p).val := by
  rw [rootCompleted_columnStar_eq]
  exact literal_star_span K U (columnMaximalExtension K p)

theorem completed_rowStar_span (U : RootPoints K)
    (q : CFSGOrthogonalDIndexTrialityD2Coordinates.RulingParameters K) :
    originalCliqueSpan K (rootCompletedClique K (neighborRowStar K U q)) =
      (rowMaximalExtension K q).val := by
  rw [rootCompleted_rowStar_eq]
  exact literal_star_span K U (rowMaximalExtension K q)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
