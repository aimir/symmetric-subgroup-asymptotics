import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedWordOrder

/-! The already checked actual Co3 word has element order divisible
by14. Its factor2 discharges parity without a new matrix-square pilot. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem co3_even_card
    (hn : ¬IsMulCommutative CFSG.Models.MatrixGroups.Co3.Model) :
    Even (Nat.card CFSG.Models.MatrixGroups.Co3.Model) := by
  obtain ⟨g,hg⟩ := CFSGCoThreeSelectedWordOrder.exists_fourteen_dvd_orderOf hn
  apply even_iff_two_dvd.mpr
  exact (by decide : 2 ∣ 14).trans (hg.trans (orderOf_dvd_natCard g))

end SymmetricSubgroupAsymptotics.CFSGReduction
