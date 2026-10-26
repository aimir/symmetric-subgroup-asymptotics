import SymmetricSubgroupAsymptotics.PrimitiveSocleTitsActualOrdinaryPacket
import SymmetricSubgroupAsymptotics.OriginalNonaffineBoundedSharpCFSGReduction

/-! Bounded sharp Tits consumer from the actual simple rank, outer
multiplicity, least index, and primitive degree form. No classification
callback, ordinary permutation input, or finite catalogue is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTitsBoundedSharp
open PrimitiveSocleRawStructure
open PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

theorem genRank_le_sharpFloor (e : D.Simple ≃* CFSG.Index.tits.Model)
    (hsmall : Nat.card X ≤ 21) :
    MarkedC4.genRank G ≤ TraceySharpHalfDegreeNumerics.sharpFloor (Nat.card X) := by
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have h14 := PrimitiveSocleTitsActualOrdinaryPacket.least_index_fourteen_le D e ell hell
  have hdegree := PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell
  have horder := (PrimitiveSocleTitsActualOrdinaryPacket.packet D e ell hell).1
  have hpower := primitiveSocle_power_le_degree (by omega : 5 ≤ ell) horder (D.degreeForm hell)
  have hk : D.factorCount = 1 := by
    by_contra hne
    have hk2 : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
    have hsquare := (Nat.pow_le_pow_right (by omega : 0 < ell) hk2).trans hpower
    nlinarith only [hsquare, h14, hsmall]
  have hrec := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_outer_multiplicity D hk
  have hs := PrimitiveSocleTitsActualOrdinaryPacket.simple_genRank_le_four D e
  have ho := PrimitiveSocleTitsActualOrdinaryPacket.outer_cardFactors_le_two D e
  have h6 : MarkedC4.genRank G ≤ 6 := by omega
  exact h6.trans (OriginalNonaffineBoundedSharpCFSGReduction.six_le_sharpFloor_of_band
    (Nat.card X) (by omega) hsmall)

end SymmetricSubgroupAsymptotics.PrimitiveSocleTitsBoundedSharp
