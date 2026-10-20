import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Joint normal-kernel indices in a fixed original source. The surviving
whole normal subgroup is charged by its top image and its literal kernel
fibre together. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.NormalKernelProjectedIndex

variable {G P Q : Type*} [Group G] [Finite G] [Group P] [Group Q]

/-- The normal quotient order factors through the top projection and
the restricted map on the actual projection kernel. -/
theorem quotient_card_eq (D : Subgroup G) [D.Normal]
    (π : G →* P) (f : G →* Q) :
    Nat.card (D.map (QuotientGroup.mk' ((D ⊓ π.ker) ⊓ f.ker))) =
      Nat.card (D.map π) * Nat.card ((D ⊓ π.ker).map f) := by
  let E := D ⊓ π.ker
  let H := E ⊓ f.ker
  have hHE : H ≤ E := inf_le_left
  have hED : E ≤ D := inf_le_left
  calc
    Nat.card (D.map (QuotientGroup.mk' H)) = H.relIndex D := by
      simpa only [QuotientGroup.ker_mk'] using
        (D.relIndex_ker (QuotientGroup.mk' H)).symm
    _ = H.relIndex E * E.relIndex D :=
      (Subgroup.relIndex_mul_relIndex H E D hHE hED).symm
    _ = Nat.card (E.map f) * Nat.card (D.map π) := by
      rw [show H.relIndex E = f.ker.relIndex E from
        Subgroup.inf_relIndex_left E f.ker,
        show E.relIndex D = π.ker.relIndex D from
          Subgroup.inf_relIndex_left D π.ker,
        E.relIndex_ker, D.relIndex_ker]
    _ = _ := Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.NormalKernelProjectedIndex
