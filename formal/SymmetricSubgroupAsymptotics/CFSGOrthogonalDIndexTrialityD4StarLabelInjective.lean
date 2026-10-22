import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarPointClasses
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CliqueSpan

/-! Original global star-clique sets recover BOTH their point and
maximal-space labels. Thus the star graph is a genuine graph of sets
of original planes, not an unproved choice of geometric parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4CliqueSpan
variable (K : Type) [Field K]

theorem pointStar_span (S : PointStarLabels K) :
    originalCliqueSpan K (pointStarPlanes K S) = S.val.2.val := by
  have hs : {P : Submodule K (Index 4 → K) | ∃ L ∈ pointStarPlanes K S, L.val = P} =
      {P : Submodule K (Index 4 → K) | Module.finrank K P = 2 ∧ S.val.1 ≤ P ∧ P ≤ S.val.2.val} := by
    ext P
    constructor
    · rintro ⟨L, hL, rfl⟩
      exact ⟨L.property.1, hL⟩
    · intro hP
      exact ⟨⟨P, hP.1, fun x hx => S.val.2.property.2 x (hP.2.2 hx)⟩, hP.2, rfl⟩
  unfold originalCliqueSpan
  rw [hs]
  exact star_planes_span_space S.val.1 S.val.2.val S.property.1 S.property.2
    (by rw [S.val.2.property.1]; decide)

theorem pointStar_has_two_planes (S : PointStarLabels K) :
    ∃ P Q : SingularPlanes K 0, P ∈ pointStarPlanes K S ∧ Q ∈ pointStarPlanes K S ∧ P ≠ Q := by
  have hM : 2 ≤ Module.finrank K S.val.2.val := by rw [S.val.2.property.1]; decide
  obtain ⟨P0, hd0, hU0, h0M, _⟩ := line_star_covers_space S.val.1 S.val.2.val
    S.property.1 S.property.2 hM 0 S.val.2.val.zero_mem
  have hn : ¬ S.val.2.val ≤ P0 := by
    intro h
    have hd := Submodule.finrank_mono h
    rw [S.val.2.property.1, hd0] at hd
    omega
  obtain ⟨x, hxM, hx0⟩ := Set.not_subset.mp hn
  obtain ⟨P1, hd1, hU1, h1M, hx1⟩ := line_star_covers_space S.val.1 S.val.2.val
    S.property.1 S.property.2 hM x hxM
  let P : SingularPlanes K 0 := ⟨P0, hd0, fun x hx => S.val.2.property.2 x (h0M hx)⟩
  let Q : SingularPlanes K 0 := ⟨P1, hd1, fun x hx => S.val.2.property.2 x (h1M hx)⟩
  refine ⟨P, Q, ⟨hU0, h0M⟩, ⟨hU1, h1M⟩, ?_⟩
  intro he
  have hh : P0 = P1 := congrArg Subtype.val he
  apply hx0
  rw [hh]
  exact hx1

theorem pointStarPlanes_injective : Function.Injective (pointStarPlanes K) := by
  intro S T he
  obtain ⟨P, Q, hP, hQ, hne⟩ := pointStar_has_two_planes K S
  have hPc : P ∈ pointStarPlanes K S ∩ pointStarPlanes K T := ⟨hP, by rw [← he]; exact hP⟩
  have hQc : Q ∈ pointStarPlanes K S ∩ pointStarPlanes K T := ⟨hQ, by rw [← he]; exact hQ⟩
  have hU := global_star_two_common_force_point_eq K _ _ _ _ S.property.1 T.property.1 P Q hPc hQc hne
  have hM := congrArg (originalCliqueSpan K) he
  rw [pointStar_span, pointStar_span] at hM
  exact Subtype.ext (Prod.ext hU (Subtype.ext hM))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
