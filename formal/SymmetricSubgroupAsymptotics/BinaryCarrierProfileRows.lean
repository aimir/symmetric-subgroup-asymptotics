import SymmetricSubgroupAsymptotics.PrimeDerivedOrderTwoProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory

/-! The six natural-number invariants of an original normal subgroup
are the exact carrier row, after casting its two quotient slopes to the
reals. This bridge changes no normal axis and assumes no numerical bound. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierProfileRows

open FullSubdirectGoursat

def rowOfProfile (v : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : JointCapacityRow :=
  ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, (v.2.2.2.2.1 : ℝ), (v.2.2.2.2.2 : ℝ)⟩

theorem actualRow_eq_profile {A : BinaryCarrierWord.Factor}
    (N : NormalAxis A.Carrier) :
    BinaryCarrierWord.actualRow N =
      rowOfProfile (PrimeDerivedOrderTwoProfiles.profile N.1) := rfl

theorem actualRow_eq_of_profile {A : BinaryCarrierWord.Factor}
    (N : NormalAxis A.Carrier) (v : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
    (h : PrimeDerivedOrderTwoProfiles.profile N.1 = v) :
    BinaryCarrierWord.actualRow N = rowOfProfile v := by
  rw [actualRow_eq_profile, h]

/-- An exhaustive profile alternative retains every original normal,
including different normals whose six invariants agree. -/
theorem actualRow_two_cases_of_profile {A : BinaryCarrierWord.Factor}
    (N : NormalAxis A.Carrier) (v w : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
    (h : PrimeDerivedOrderTwoProfiles.profile N.1 = v ∨
      PrimeDerivedOrderTwoProfiles.profile N.1 = w) :
    BinaryCarrierWord.actualRow N = rowOfProfile v ∨
      BinaryCarrierWord.actualRow N = rowOfProfile w := by
  rcases h with h | h
  · exact Or.inl (actualRow_eq_of_profile N v h)
  · exact Or.inr (actualRow_eq_of_profile N w h)

end SymmetricSubgroupAsymptotics.BinaryCarrierProfileRows
