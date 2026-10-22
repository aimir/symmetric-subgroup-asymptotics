import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4QuadraticStarIntersections
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4DualPolarFixedSpace

/-! The connected classes of ORIGINAL point/maximal-space star labels,
joined by TWO distinct common original planes, are EXACTLY the original
point labels. The converse is proved by fixed-space dual-polar paths;
no residual quotient or connectedness assumption is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexTrialityD4PolarHyperplane
variable (K : Type) [Field K]

def PointStarLabels :=
  {p : Submodule K (Index 4 → K) × MaximalSingular (splitQuadraticForm K 4) 4 //
    Module.finrank K p.1 = 1 ∧ p.1 ≤ p.2.val}

def pointStarPlanes (S : PointStarLabels K) : Set (SingularPlanes K 0) :=
  globalStarPlanes K S.val.1 S.val.2.val

def SharedStarPair (S T : PointStarLabels K) : Prop :=
  ∃ P Q : SingularPlanes K 0, P ≠ Q ∧ P ∈ pointStarPlanes K S ∩ pointStarPlanes K T ∧
    Q ∈ pointStarPlanes K S ∩ pointStarPlanes K T

theorem sharedStarPair_point_eq (S T : PointStarLabels K) (h : SharedStarPair K S T) :
    S.val.1 = T.val.1 := by
  obtain ⟨P, Q, hne, hP, hQ⟩ := h
  exact global_star_two_common_force_point_eq K _ _ _ _ S.property.1 T.property.1 P Q hP hQ hne

theorem sharedStarPair_path_point_eq (S T : PointStarLabels K)
    (h : Relation.ReflTransGen (SharedStarPair K) S T) : S.val.1 = T.val.1 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (sharedStarPair_point_eq K _ _ hstep)

theorem same_point_dual_edge_shared_pair [Finite K] (S T : PointStarLabels K)
    (hU : S.val.1 = T.val.1)
    (hcap : Module.finrank K ↥(S.val.2.val ⊓ T.val.2.val) = 3) : SharedStarPair K S T := by
  have hUT : S.val.1 ≤ T.val.2.val := by rw [hU]; exact T.property.2
  let C := {P : SingularPlanes K 0 // P ∈ pointStarPlanes K S ∩ pointStarPlanes K T}
  have hc : Nat.card C = Nat.card K + 1 := by
    change Nat.card {P : SingularPlanes K 0 // P ∈ globalStarPlanes K S.val.1 S.val.2.val ∩
      globalStarPlanes K T.val.1 T.val.2.val} = _
    rw [← hU]
    exact global_same_point_star_intersection_card K _ _ _ S.val.2.property.2 S.property.2 hUT S.property.1 hcap
  have hpos : 0 < Nat.card K := Nat.card_pos
  letI : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  letI : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; omega)
  obtain ⟨P, Q, hne⟩ := exists_pair_ne C
  exact ⟨P.val, Q.val, (fun he => hne (Subtype.ext he)), P.property, Q.property⟩

theorem pointStar_connected_iff_point_eq [Finite K] (S T : PointStarLabels K) :
    Relation.ReflTransGen (SharedStarPair K) S T ↔ S.val.1 = T.val.1 := by
  constructor
  · exact sharedStarPair_path_point_eq K S T
  · intro hU
    let U := S.val.1
    let A : ContainingMaximalSingular (splitQuadraticForm K 4) 4 U := ⟨S.val.2, S.property.2⟩
    let B : ContainingMaximalSingular (splitQuadraticForm K 4) 4 U :=
      ⟨T.val.2, by change S.val.1 ≤ T.val.2.val; rw [hU]; exact T.property.2⟩
    let e : ContainingMaximalSingular (splitQuadraticForm K 4) 4 U → PointStarLabels K :=
      fun M => ⟨(U, M.val), S.property.1, M.property⟩
    have hp := fixed_space_dual_polar_connected (splitQuadraticForm K 4)
      (splitQuadraticForm_nondegenerate K 4) 4 (naturalSpace_finrank K 4) U A B
    have himage : ∀ M N : ContainingMaximalSingular (splitQuadraticForm K 4) 4 U, DualAdjacent (splitQuadraticForm K 4) 4 M.val N.val →
        SharedStarPair K (e M) (e N) := by
      intro M N hMN
      apply same_point_dual_edge_shared_pair K (e M) (e N) rfl
      have hd := hMN.2
      change Module.finrank K ↥(M.val.val ⊓ N.val.val) + 1 = 4 at hd
      change Module.finrank K ↥(M.val.val ⊓ N.val.val) = 3
      omega
    have hh := Relation.ReflTransGen.lift e himage hp
    have ha : e A = S := Subtype.ext rfl
    have hb : e B = T := Subtype.ext (Prod.ext hU rfl)
    rw [ha, hb] at hh
    exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
