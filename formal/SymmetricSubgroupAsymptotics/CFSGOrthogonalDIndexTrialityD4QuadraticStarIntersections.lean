import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarIntersections
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalCliqueTypes

/-! Actual quadratic star-clique intersections on ORIGINAL singular
planes. Distinct point labels have at most one common plane; a common
point and three-dimensional maximal-space intersection yield q+1.
No polar-selfzero weakening is made in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexTrialityD4StarIntersections
variable (K : Type) [Field K]

def globalStarPlanes (U M : Submodule K (Index 4 → K)) : Set (SingularPlanes K 0) :=
  {P | U ≤ P.val ∧ P.val ≤ M}

theorem global_star_two_common_force_point_eq
    (U W M N : Submodule K (Index 4 → K))
    (hU : Module.finrank K U = 1) (hW : Module.finrank K W = 1)
    (P Q : SingularPlanes K 0)
    (hP : P ∈ globalStarPlanes K U M ∩ globalStarPlanes K W N)
    (hQ : Q ∈ globalStarPlanes K U M ∩ globalStarPlanes K W N) (hne : P ≠ Q) : U = W :=
  two_common_star_planes_force_point_eq U W M N P.val Q.val hU hW
    ⟨⟨P.property.1, hP.1⟩, ⟨P.property.1, hP.2⟩⟩
    ⟨⟨Q.property.1, hQ.1⟩, ⟨Q.property.1, hQ.2⟩⟩
    (fun he => hne (Subtype.ext he))

def actualStarIntersectionEquiv (U M N : Submodule K (Index 4 → K))
    (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0) :
    {P : SingularPlanes K 0 // P ∈ globalStarPlanes K U M ∩ globalStarPlanes K U N} ≃
      {P : Submodule K (Index 4 → K) // P ∈ RawStar U M ∩ RawStar U N} where
  toFun P := ⟨P.val.val, ⟨P.val.property.1, P.property.1⟩, ⟨P.val.property.1, P.property.2⟩⟩
  invFun P := ⟨⟨P.val, P.property.1.1,
    fun x hx => hM x (P.property.1.2.2 hx)⟩, P.property.1.2, P.property.2.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

theorem global_same_point_star_intersection_card [Finite K]
    (U M N : Submodule K (Index 4 → K))
    (hM : ∀ x ∈ M, splitQuadraticForm K 4 x = 0)
    (hUM : U ≤ M) (hUN : U ≤ N) (hU : Module.finrank K U = 1)
    (hMN : Module.finrank K ↥(M ⊓ N) = 3) :
    Nat.card {P : SingularPlanes K 0 // P ∈ globalStarPlanes K U M ∩ globalStarPlanes K U N} =
      Nat.card K + 1 :=
  (Nat.card_congr (actualStarIntersectionEquiv K U M N hM)).trans
    (samePointStarIntersection_card U M N hUM hUN hU hMN)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
