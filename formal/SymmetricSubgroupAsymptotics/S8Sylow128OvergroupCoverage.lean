import SymmetricSubgroupAsymptotics.FiniteOvergroupJoinCoverage
import SymmetricSubgroupAsymptotics.S8Sylow128CanonicalAnchorBindings
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot0
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot1
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot2
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot3
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot4
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot5
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot6
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot7
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot8
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot9
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot10
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot11
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot12
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot13
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot14
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralRoot15
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin0_0
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin0_1
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin0_2
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin0_3
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin1_0
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin1_1
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin1_2
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin1_3
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin2_0
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin2_1
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin2_2
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin2_3
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin3_0
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin3_1
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin3_2
import SymmetricSubgroupAsymptotics.S8Sylow128LiteralJoin3_3
import Mathlib.Tactic.FinCases

/-! Complete selected overgroup coverage above the literal original8T35
seed. All sixteen exact seed adjunctions and the complete literal join table
have separate ordinary-word proofs. Canonical correspondence retains the
actual checked point conjugators; no abstract-order recognition is used.
This is one seed case, not the full degree-eight action classification. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Sylow128OvergroupCoverage
open S8Sylow128LeftCosets
open FiniteSubgroupAdjunctionCoverage

theorem exact_seed_adjoin (g : Ambient) : ∃ j : Fin 4,
    H ⊔ Subgroup.closure {g} = S8Sylow128LiteralModels.rows j := by
  obtain ⟨k, hk⟩ := S8Sylow128DoubleCosets.covers_adjoin g
  fin_cases k
  · exact ⟨0, hk.trans S8Sylow128LiteralRoot0.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot1.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot2.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot3.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot4.exact_eq⟩
  · exact ⟨1, hk.trans S8Sylow128LiteralRoot5.exact_eq⟩
  · exact ⟨2, hk.trans S8Sylow128LiteralRoot6.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot7.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot8.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot9.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot10.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot11.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot12.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot13.exact_eq⟩
  · exact ⟨3, hk.trans S8Sylow128LiteralRoot14.exact_eq⟩
  · exact ⟨2, hk.trans S8Sylow128LiteralRoot15.exact_eq⟩

theorem exact_join (i j : Fin 4) : ∃ k : Fin 4,
    S8Sylow128LiteralModels.rows i ⊔ S8Sylow128LiteralModels.rows j =
      S8Sylow128LiteralModels.rows k := by
  fin_cases i <;> fin_cases j
  · exact ⟨0, S8Sylow128LiteralJoin0_0.exact_eq⟩
  · exact ⟨1, S8Sylow128LiteralJoin0_1.exact_eq⟩
  · exact ⟨2, S8Sylow128LiteralJoin0_2.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin0_3.exact_eq⟩
  · exact ⟨1, S8Sylow128LiteralJoin1_0.exact_eq⟩
  · exact ⟨1, S8Sylow128LiteralJoin1_1.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin1_2.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin1_3.exact_eq⟩
  · exact ⟨2, S8Sylow128LiteralJoin2_0.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin2_1.exact_eq⟩
  · exact ⟨2, S8Sylow128LiteralJoin2_2.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin2_3.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin3_0.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin3_1.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin3_2.exact_eq⟩
  · exact ⟨3, S8Sylow128LiteralJoin3_3.exact_eq⟩

theorem complete_literal (U : Subgroup Ambient) (hHU : H ≤ U) :
    Covered S8Sylow128LiteralModels.rows U :=
  complete_above_of_seed_adjunctions_and_joins H S8Sylow128LiteralModels.rows
    S8Sylow128LiteralModels.contains_seed ⟨0, S8Sylow128LiteralModels.row_zero⟩
    exact_seed_adjoin exact_join hHU

theorem literal_binding (i : Fin 4) :
    Covered S8Sylow128SelectedRows.rows (S8Sylow128LiteralModels.rows i) :=
  S8Sylow128CanonicalAnchorBindings.binding i

/-- Every actual overgroup of this fixed seed is point-conjugate to one of
the displayed canonical actions. -/
theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) :
    Covered S8Sylow128SelectedRows.rows U := by
  obtain ⟨i, c, hc⟩ := complete_literal U hHU
  obtain ⟨j, d, hd⟩ := literal_binding i
  refine ⟨j, d * c, ?_⟩
  rw [map_mul, mul_smul, hc, hd]

end SymmetricSubgroupAsymptotics.S8Sylow128OvergroupCoverage
end
