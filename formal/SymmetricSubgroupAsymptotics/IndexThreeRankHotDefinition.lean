import SymmetricSubgroupAsymptotics.ScalarFourHeadDefinitions
import SymmetricSubgroupAsymptotics.BinaryRankHotDefinition

/-! # Index-three binary-rank hot sources -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- Some index-three kernel of the complete source has `d₂ > a b`. -/
def IndexThreeRankHot (a : ℝ) {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    Prop :=
  ∃ θ : J →* CyclicThree, Function.Surjective θ ∧
    a * b < binaryCharacterRank θ.ker

theorem indexThreeRank_le_of_not_hot {a : ℝ} {b : ℕ}
    {J : Subgroup (Equiv.Perm (Fin b))} (hJ : ¬ IndexThreeRankHot a J)
    (θ : J →* CyclicThree) (hθ : Function.Surjective θ) :
    (binaryCharacterRank θ.ker : ℝ) ≤ a * b := by
  by_contra hlt
  exact hJ ⟨θ, hθ, lt_of_not_ge hlt⟩

end SymmetricSubgroupAsymptotics

end
