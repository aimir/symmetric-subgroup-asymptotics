import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.End

/-! The stabilizer of ONE actual permutation type has index at most
the number of types. This keeps the other two types free to exchange. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeIndex
variable {G T : Type*} [Group G]

def pointStabilizer (pi : G →* Equiv.Perm T) (t : T) : Subgroup G :=
  (MulAction.stabilizer (Equiv.Perm T) t).comap pi

def pointCoset (pi : G →* Equiv.Perm T) (t : T) : G ⧸ pointStabilizer pi t → T :=
  Quotient.lift (fun g => pi g t) (by
    intro g h hrel
    have hh := QuotientGroup.leftRel_apply.mp hrel
    change pi (g⁻¹ * h) t = t at hh
    rw [map_mul, map_inv] at hh
    change (pi g)⁻¹ (pi h t) = t at hh
    have hc := congrArg (pi g) hh
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hc.symm)

theorem pointCoset_injective (pi : G →* Equiv.Perm T) (t : T) :
    Function.Injective (pointCoset pi t) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro g h he
  apply Quotient.sound
  apply QuotientGroup.leftRel_apply.mpr
  change pi (g⁻¹ * h) t = t
  change pi g t = pi h t at he
  rw [map_mul, map_inv]
  change (pi g)⁻¹ (pi h t) = t
  rw [← he]
  exact Equiv.symm_apply_apply (pi g) t

theorem pointStabilizer_index_le [Finite T] (pi : G →* Equiv.Perm T) (t : T) :
    (pointStabilizer pi t).index ≤ Nat.card T :=
  Nat.card_le_card_of_injective (pointCoset pi t) (pointCoset_injective pi t)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeIndex
