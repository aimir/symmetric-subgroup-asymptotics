import SymmetricSubgroupAsymptotics.CFSGPrimeBinaryMinimalNormal
import SymmetricSubgroupAsymptotics.CFSGSelfCentralizingMinimalNormal
import SymmetricSubgroupAsymptotics.CFSGSmallLinearSimpleOuterOrder
import SymmetricSubgroupAsymptotics.PrimitiveSocleCentralizerRegular
import SymmetricSubgroupAsymptotics.FixedTargetCompositionTrace
import SymmetricSubgroupAsymptotics.UniqueMinimalNormalAbelianLength

/-! Every chosen original chief series of a nonsoluble faithful irreducible binary
linear group in dimension5 has abelian charge at most4. The simple normal
subgroup and its quotient are derived from the original action, rather than
identified by a finite list of matrix subgroups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveBinaryFiveChiefBound

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Finite V]

theorem chief_abelianLength_le_four
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (rho : Representation (ZMod 2) G V)
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 5) (hns : ¬ IsSolvable G)
    (c : ActualChiefSeries G) : actualChiefSeriesAbelianLength c ≤ 4 := by
  have hnt : ¬ Subsingleton G := by
    intro hs
    letI : Subsingleton G := hs
    exact hns inferInstance
  letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hnt
  letI : Fact (Nat.Prime 31) := ⟨by decide⟩
  have hdim : (Module.finrank (ZMod 2) V).Prime := by rw [hd]; decide
  have hV : Nat.card V = 32 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  have hcard : Nat.card V - 1 = 31 := by rw [hV]
  obtain ⟨E, hE⟩ := PrimitiveSocleONanScottHelpers.exists_minimalNormal (G := G)
  letI : E.Normal := hE.1
  have hnc : ¬ IsMulCommutative E := by
    intro hc
    letI : IsMulCommutative E := hc
    exact hns (CFSGPrimeBinaryAbelianNormal.soluble_of_nontrivial_abelian_normal_dimension_five
      rho hrho hf hd E hE.2.1)
  letI : IsSimpleGroup E := CFSGPrimeBinaryMinimalNormal.minimal_normal_isSimple
    rho hrho hf hdim hcard E hE hnc
  have hC := CFSGPrimeBinaryMinimalNormal.normal_centralizer_eq_bot_of_not_solvable
    rho hrho hf hdim hcard hns E hE.2.1
  have hquot := CFSGSelfCentralizingMinimalNormal.quotient_card_le_outer E hnc hC
  have hfE : Function.Injective (rho.comp E.subtype) := by
    intro a b hab
    exact Subtype.ext (hf hab)
  have hout := CFSGSmallLinearSimpleOuterOrder.outer_card_le_thirty_of_module_card_le_thirtyTwo
    hindex (rho.comp E.subtype) hfE hnc hV.le
  have hsmall : ArithmeticFunction.cardFactors (Nat.card (G ⧸ E)) ≤ 4 :=
    CFSGSmallLinearSimpleOuterOrder.cardFactors_le_four_of_le_thirtyOne _
      ((hquot.trans hout).trans (by decide : 30 ≤ 31))
  exact (actualChiefSeriesAbelianLength_le_quotient_cardFactors c E hE.2.1 hnc
    (fun N hN hn => by
      letI : N.Normal := hN
      exact CFSGSelfCentralizingMinimalNormal.le_every_nontrivial_normal E hE hC N hn)).trans hsmall

end SymmetricSubgroupAsymptotics.CFSGPrimitiveBinaryFiveChiefBound
