import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4BoundedPencil

/-! Two distinct original planes common to two point-stars force the
SAME point. Stars at one point whose containing spaces meet in a
three-space share an actual q+1 pencil. These are linear facts in all
characteristics, before the residual connectivity argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarIntersections
open CFSGOrthogonalDIndexTrialityD4LinePencil
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def RawStar (U M : Submodule K V) : Set (Submodule K V) :=
  {P | Module.finrank K P = 2 ∧ U ≤ P ∧ P ≤ M}

private theorem line_inf_bot (U W : Submodule K V) (hU : Module.finrank K U = 1)
    (hW : Module.finrank K W = 1) (hne : U ≠ W) : U ⊓ W = ⊥ := by
  have hhi := Submodule.finrank_mono (inf_le_left : U ⊓ W ≤ U)
  rw [hU] at hhi
  by_cases hz : Module.finrank K ↥(U ⊓ W) = 0
  · exact Submodule.finrank_eq_zero.mp hz
  · have hd : Module.finrank K ↥(U ⊓ W) = 1 := by omega
    have heU : U ⊓ W = U := Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hd, hU])
    have heW : U ⊓ W = W := Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [hd, hW])
    exact False.elim (hne (heU.symm.trans heW))

theorem common_star_plane_unique (U W M N P Q : Submodule K V)
    (hU : Module.finrank K U = 1) (hW : Module.finrank K W = 1) (hne : U ≠ W)
    (hP : P ∈ RawStar U M ∩ RawStar W N) (hQ : Q ∈ RawStar U M ∩ RawStar W N) : P = Q := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [line_inf_bot U W hU hW hne, finrank_bot, hU, hW] at hd
  have hdim : Module.finrank K ↥(U ⊔ W) = 2 := by omega
  have heP : U ⊔ W = P := Submodule.eq_of_le_of_finrank_le
    (sup_le hP.1.2.1 hP.2.2.1) (by rw [hdim, hP.1.1])
  have heQ : U ⊔ W = Q := Submodule.eq_of_le_of_finrank_le
    (sup_le hQ.1.2.1 hQ.2.2.1) (by rw [hdim, hQ.1.1])
  exact heP.symm.trans heQ

theorem two_common_star_planes_force_point_eq (U W M N P Q : Submodule K V)
    (hU : Module.finrank K U = 1) (hW : Module.finrank K W = 1)
    (hP : P ∈ RawStar U M ∩ RawStar W N) (hQ : Q ∈ RawStar U M ∩ RawStar W N)
    (hne : P ≠ Q) : U = W := by
  by_contra hUW
  exact hne (common_star_plane_unique U W M N P Q hU hW hUW hP hQ)

def samePointStarIntersectionEquiv (U M N : Submodule K V) :
    {P : Submodule K V // P ∈ RawStar U M ∩ RawStar U N} ≃ PlaneInterval U (M ⊓ N) where
  toFun P := ⟨P.val, P.property.1.1, P.property.1.2.1,
    le_inf P.property.1.2.2 P.property.2.2.2⟩
  invFun P := ⟨P.val, ⟨P.property.1, P.property.2.1, P.property.2.2.trans inf_le_left⟩,
    ⟨P.property.1, P.property.2.1, P.property.2.2.trans inf_le_right⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem samePointStarIntersection_card [Finite K] (U M N : Submodule K V)
    (hUM : U ≤ M) (hUN : U ≤ N) (hU : Module.finrank K U = 1)
    (hMN : Module.finrank K ↥(M ⊓ N) = 3) :
    Nat.card {P : Submodule K V // P ∈ RawStar U M ∩ RawStar U N} = Nat.card K + 1 :=
  (Nat.card_congr (samePointStarIntersectionEquiv U M N)).trans
    (planeInterval_card U (M ⊓ N) (le_inf hUM hUN) hU hMN)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4StarIntersections
