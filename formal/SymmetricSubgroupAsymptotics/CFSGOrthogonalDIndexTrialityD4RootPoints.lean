import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NeighborFlags
import Mathlib.Data.Finite.Card

/-! The original intersection-point coordinate in the D4 residue is
the actual projective line of the original root plane. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices
variable (K : Type) [Field K]

def rootPointRestrictionEquiv : RootPoints K ≃
    {L : Submodule K (rootPlane K) // Module.finrank K L = 1} where
  toFun U := ⟨U.val.comap (rootPlane K).subtype,
    (Submodule.comapSubtypeEquivOfLe U.property.2).finrank_eq.trans U.property.1⟩
  invFun L := ⟨L.val.map (rootPlane K).subtype,
    (Submodule.finrank_map_subtype_eq (rootPlane K) L.val).trans L.property, by
      rintro x ⟨u, hu, rfl⟩
      exact u.property⟩
  left_inv U := Subtype.ext ((Submodule.map_comap_subtype (rootPlane K) U.val).trans
    (inf_eq_right.mpr U.property.2))
  right_inv L := Subtype.ext
    (Submodule.comap_map_eq_of_injective (rootPlane K).subtype_injective L.val)

def rootPointProjectiveEquiv : RootPoints K ≃ ℙ K (rootPlane K) :=
  (rootPointRestrictionEquiv K).trans (Projectivization.equivSubmodule K (rootPlane K)).symm

theorem rootPoints_card [Finite K] : Nat.card (RootPoints K) = Nat.card K + 1 :=
  (Nat.card_congr (rootPointProjectiveEquiv K)).trans
    (Projectivization.card_of_finrank_two K (rootPlane K) (rootPlane_finrank K))

theorem rootPoints_nontrivial [Finite K] : Nontrivial (RootPoints K) := by
  have hc := rootPoints_card K
  letI : Finite (RootPoints K) := Nat.finite_of_card_ne_zero (by rw [hc]; omega)
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [hc]
  have hp : 0 < Nat.card K := Nat.card_pos
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
