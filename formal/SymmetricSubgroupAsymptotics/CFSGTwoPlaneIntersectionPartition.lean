import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-! Distinct two-dimensional submodules either are disjoint or meet
in one dimension. This elementary partition uses the same submodules. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionPartition
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem inf_finrank_le_one (P Q : Submodule K V)
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2) (hne : P ≠ Q) :
    Module.finrank K (P ⊓ Q : Submodule K V) ≤ 1 := by
  by_contra hn
  have hlarge : 2 ≤ Module.finrank K (P ⊓ Q : Submodule K V) := by omega
  have he : P ⊓ Q = P :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hP]; exact hlarge)
  have hle : P ≤ Q := he.ge.trans inf_le_right
  exact hne (Submodule.eq_of_le_of_finrank_le hle (by rw [hP, hQ]))

theorem inf_finrank_eq_one_of_not_disjoint (P Q : Submodule K V)
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hne : P ≠ Q) (hd : ¬Disjoint P Q) :
    Module.finrank K (P ⊓ Q : Submodule K V) = 1 := by
  have hbot : (P ⊓ Q : Submodule K V) ≠ ⊥ :=
    fun he => hd (disjoint_iff.mpr he)
  have hlo : 1 ≤ Module.finrank K (P ⊓ Q : Submodule K V) :=
    Submodule.one_le_finrank_iff.mpr hbot
  exact Nat.le_antisymm (inf_finrank_le_one P Q hP hQ hne) hlo

theorem disjoint_or_inf_finrank_eq_one (P Q : Submodule K V)
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2) (hne : P ≠ Q) :
    Disjoint P Q ∨ Module.finrank K (P ⊓ Q : Submodule K V) = 1 := by
  by_cases hd : Disjoint P Q
  · exact Or.inl hd
  · exact Or.inr (inf_finrank_eq_one_of_not_disjoint P Q hP hQ hne hd)

end SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionPartition
