import SymmetricSubgroupAsymptotics.SubdirectTailImage
import SymmetricSubgroupAsymptotics.BinaryMarkedInvariantsCongr
import SymmetricSubgroupAsymptotics.BinaryMarkedGoursatPeel

/-! Install the three-invariant transport on the literal complete tail.
An original product subgroup and its actual full core have identical marks.
The one-peel transition can therefore be used without assuming a global
word recurrence or replacing the tail subgroup by an unrelated group.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryMarkedGoursatPeel

theorem exponent_congr {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (x y z : ℝ) : exponent G x y z = exponent H x y z := by
  unfold exponent
  rw [binaryCharacterRank_congr e,primeDerivedNormalRank_congr 2 e,
    terminalRestrictedInflationKernel_finrank_congr e]

theorem mark_congr {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (x y z : ℝ) : mark G x y z = mark H x y z :=
  congrArg (fun t : ℝ => (2 : ℝ)^t) (exponent_congr e x y z)

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

/-- The original d, rho, and actual H² defect are all retained together. -/
theorem original_mark_eq_core (H : Subgroup (A × B)) (x y z : ℝ) :
    mark H x y z = mark (SubdirectTailImage.core H) x y z :=
  mark_congr (SubdirectTailImage.equiv H) x y z

/-- The normal index seen by the core is the literal original first axis,
including its whole-A normality. -/
theorem original_axis_eq (H : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ H.subtype)) :
    FullSubdirectGoursat.axis (SubdirectTailImage.full H hA) =
      (⟨H.goursatFst,Subgroup.normal_goursatFst hA⟩ : FullSubdirectGoursat.NormalAxis A) :=
  Subtype.ext (SubdirectTailImage.core_axis H)

/-- A marked transition for the original H, over its exact complete tail
image. Every displayed row is still computed on the same original axis. -/
theorem original_mark_le (H : Subgroup (A × B))
    (hA : Function.Surjective (Prod.fst ∘ H.subtype))
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    mark H x y z ≤ mark (SubdirectTailImage.tail H) x y z *
      (2 : ℝ)^(cost (⟨H.goursatFst,Subgroup.normal_goursatFst hA⟩ :
        FullSubdirectGoursat.NormalAxis A) x y z) := by
  rw [original_mark_eq_core H x y z]
  have h := mark_le (SubdirectTailImage.full H hA) x y z hy hz
  rwa [original_axis_eq H hA] at h

end BinaryMarkedGoursatPeel
end SymmetricSubgroupAsymptotics
