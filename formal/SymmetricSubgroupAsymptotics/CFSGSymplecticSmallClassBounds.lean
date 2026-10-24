import SymmetricSubgroupAsymptotics.CFSGSymplecticClassCodeBounds
import SymmetricSubgroupAsymptotics.CFSGSymplecticPointClassRecurrence
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Unconditional small-field class bounds on the actual original
elementary symplectic groups and their actual point stabilizers. The
same finite primary code supplies rank one and the higher-rank steps;
no separate rank-one classification or class-count premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds
open CFSGSymplecticSerreMatrices CFSGSymplecticPointAffineHom
open CFSGSymplecticClassCodeBounds CFSGSymplecticPointClassExtension
open CFSGSymplecticPointClassRecurrence
variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem binary_small (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (pointStabilizer K 0)) ≤ 2 ∧
    Nat.card (ConjClasses (elementaryRootGroup K 1)) ≤ 4 ∧
    Nat.card (ConjClasses (pointStabilizer K 1)) ≤ 12 ∧
    Nat.card (ConjClasses (elementaryRootGroup K 2)) ≤ 20 ∧
    Nat.card (ConjClasses (pointStabilizer K 2)) ≤ 64 ∧
    Nat.card (ConjClasses (elementaryRootGroup K 3)) ≤ 96 ∧
    Nat.card (ConjClasses (pointStabilizer K 3)) ≤ 320 ∧
    Nat.card (ConjClasses (elementaryRootGroup K 4)) ≤ 448 ∧
    Nat.card (ConjClasses (elementaryRootGroup K 4)) +
      Nat.card (ConjClasses (pointStabilizer K 3)) ≤ 768 := by
  have hp₀ := rankOne_class_card_le K
  have hs₁ := class_card_le_binary K hK 0
  have hs₂ := class_card_le_binary K hK 1
  have hs₃ := class_card_le_binary K hK 2
  have hs₄ := class_card_le_binary K hK 3
  have hp₁ := class_card_recurrence K 0
  have hp₂ := class_card_recurrence K 1
  have hp₃ := class_card_recurrence K 2
  norm_num [hK] at hp₀ hs₁ hs₂ hs₃ hs₄ hp₁ hp₂ hp₃
  change Nat.card (ConjClasses (elementaryRootGroup K 1)) ≤
    Nat.card (ConjClasses (pointStabilizer K 0)) + 2 at hs₁
  change Nat.card (ConjClasses (elementaryRootGroup K 2)) ≤
    Nat.card (ConjClasses (pointStabilizer K 1)) + 8 at hs₂
  change Nat.card (ConjClasses (elementaryRootGroup K 3)) ≤
    Nat.card (ConjClasses (pointStabilizer K 2)) + 32 at hs₃
  change Nat.card (ConjClasses (elementaryRootGroup K 4)) ≤
    Nat.card (ConjClasses (pointStabilizer K 3)) + 128 at hs₄
  change Nat.card (ConjClasses (pointStabilizer K 1)) ≤
    2*(Nat.card (ConjClasses (elementaryRootGroup K 1)) +
      Nat.card (ConjClasses (pointStabilizer K 0))) at hp₁
  change Nat.card (ConjClasses (pointStabilizer K 2)) ≤
    2*(Nat.card (ConjClasses (elementaryRootGroup K 2)) +
      Nat.card (ConjClasses (pointStabilizer K 1))) at hp₂
  change Nat.card (ConjClasses (pointStabilizer K 3)) ≤
    2*(Nat.card (ConjClasses (elementaryRootGroup K 3)) +
      Nat.card (ConjClasses (pointStabilizer K 2))) at hp₃
  omega

theorem binary_rankThree (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (elementaryRootGroup K 3)) ≤ 96 := by
  have h := binary_small K hK
  omega

theorem binary_rankFour (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (elementaryRootGroup K 4)) ≤ 448 := by
  have h := binary_small K hK
  omega

theorem binary_point_rankFour (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (pointStabilizer K 3)) ≤ 320 := by
  have h := binary_small K hK
  omega

theorem binary_rankFour_add_point (hK : Nat.card K = 2) :
    Nat.card (ConjClasses (elementaryRootGroup K 4)) +
      Nat.card (ConjClasses (pointStabilizer K 3)) ≤ 768 := by
  have h := binary_small K hK
  omega

theorem four_small (hK : Nat.card K = 4) :
    Nat.card (ConjClasses (elementaryRootGroup K 1)) ≤ 12 ∧
    Nat.card (ConjClasses (pointStabilizer K 1)) ≤ 64 ∧
    Nat.card (ConjClasses (elementaryRootGroup K 2)) ≤ 192 := by
  have hp₀ := rankOne_class_card_le K
  have hs₁ := class_card_le_general K 0
  have hs₂ := class_card_le_general K 1
  have hp₁ := class_card_recurrence K 0
  norm_num [hK] at hp₀ hs₁ hs₂ hp₁
  change Nat.card (ConjClasses (elementaryRootGroup K 1)) ≤
    Nat.card (ConjClasses (pointStabilizer K 0)) + 8 at hs₁
  change Nat.card (ConjClasses (elementaryRootGroup K 2)) ≤
    Nat.card (ConjClasses (pointStabilizer K 1)) + 128 at hs₂
  change Nat.card (ConjClasses (pointStabilizer K 1)) ≤
    4*(Nat.card (ConjClasses (elementaryRootGroup K 1)) +
      Nat.card (ConjClasses (pointStabilizer K 0))) at hp₁
  omega

theorem four_rankTwo (hK : Nat.card K = 4) :
    Nat.card (ConjClasses (elementaryRootGroup K 2)) ≤ 192 := by
  have h := four_small K hK
  omega

end SymmetricSubgroupAsymptotics.CFSGSymplecticSmallClassBounds
