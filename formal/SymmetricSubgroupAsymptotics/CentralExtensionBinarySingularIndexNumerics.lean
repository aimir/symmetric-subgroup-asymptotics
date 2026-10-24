import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Integer-cardinality improvement for one binary central-extension
stabilizer. The possible quotient sizes follow from its actual
subgroup-cardinality divisibility, not from a subgroup census. -/
set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CentralExtensionBinarySingularIndexNumerics

theorem index_ge_twentyFour (m w l : ℕ) (hw : 0 < w) (hwb : w ≤ 4)
    (hd : w ∣ 16) (hl : 0 < l) (he : m * w = 32 * l)
    (ho : 1 < w → 9 ≤ (w - 1) * l) : 24 ≤ m := by
  have hc : w = 1 ∨ w = 2 ∨ w = 4 := by
    interval_cases w
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · norm_num at hd
    · exact Or.inr (Or.inr rfl)
  rcases hc with rfl | rfl | rfl
  · nlinarith
  · have hh := ho (by decide : 1 < 2)
    nlinarith
  · have hh := ho (by decide : 1 < 4)
    have hl3 : 3 ≤ l := by omega
    nlinarith

end SymmetricSubgroupAsymptotics.CentralExtensionBinarySingularIndexNumerics
