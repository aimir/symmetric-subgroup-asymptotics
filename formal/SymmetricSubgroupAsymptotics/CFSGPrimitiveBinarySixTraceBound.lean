import SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixMinimalNormal
import SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixAbelianNormal
import SymmetricSubgroupAsymptotics.CFSGSelfCentralizingMinimalNormal
import SymmetricSubgroupAsymptotics.CFSGSmallLinearSimpleOuterSixtyFour
import SymmetricSubgroupAsymptotics.PrimitiveSocleCentralizerRegular
import SymmetricSubgroupAsymptotics.FixedTargetCompositionTrace
import SymmetricSubgroupAsymptotics.UniqueMinimalNormalAbelianLength

/-! The original chief trace of a faithful irreducible binary action in
dimension six has abelian charge at most fourteen. Nonhomogeneous normal
restrictions and abelian normal subgroups use the actual block/scalar order
bounds. In the remaining case a literal self-centralizing simple minimal
normal subgroup leaves a quotient with at most five prime factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixTraceBound

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [Finite V] [FiniteDimensional (ZMod 2) V]

theorem trace_abelianLength_le_fourteen
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (rho : Representation (ZMod 2) G V)
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : Module.finrank (ZMod 2) V = 6) (hn : ¬ IsSolvable G)
    (T : FixedTargetCompositionTrace G) : T.envelope.abelianLength ≤ 14 := by
  by_cases hAb : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ IsMulCommutative N
  · obtain ⟨N, hNn, hN, hNc⟩ := hAb
    letI : N.Normal := hNn
    letI : IsMulCommutative N := hNc
    exact CFSGPrimitiveBinarySixAbelianNormal.trace_le_fourteen_of_abelian_normal
      rho hrho hf hd N hN T
  have hNo : ∀ N : Subgroup G, N.Normal → IsMulCommutative N → N = ⊥ := by
    intro N hNn hNc
    by_contra hN
    exact hAb ⟨N, hNn, hN, hNc⟩
  have hnt : ¬ Subsingleton G := by
    intro hs
    letI : Subsingleton G := hs
    exact hn inferInstance
  letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hnt
  obtain ⟨E, hE⟩ := PrimitiveSocleONanScottHelpers.exists_minimalNormal (G := G)
  letI : E.Normal := hE.1
  have hnc : ¬ IsMulCommutative E := by
    intro hc
    exact hE.2.1 (hNo E hE.1 hc)
  rcases CFSGCliffordBinarySixBlockExhaustion.isotypic_or_trace_le_fourteen
      rho hrho hf hd E T with hiso | hsmall
  · letI : IsSimpleGroup E := CFSGPrimitiveBinarySixMinimalNormal.minimal_normal_isSimple
      rho hrho hf hd E hE hnc hiso
    have hC := CFSGPrimitiveBinarySixMinimalNormal.normal_centralizer_eq_bot
      rho hrho hf hd hNo E hnc hiso
    have hquot := CFSGSelfCentralizingMinimalNormal.quotient_card_le_outer E hnc hC
    have hfE : Function.Injective (rho.comp E.subtype) := by
      intro a b hab
      exact Subtype.ext (hf hab)
    have hV : Nat.card V = 64 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
      norm_num
    have hout := CFSGSmallLinearSimpleOuterSixtyFour.outer_card_le_thirtySix
      hindex (rho.comp E.subtype) hfE hnc hV.le
    have hsmall : ArithmeticFunction.cardFactors (Nat.card (G ⧸ E)) ≤ 5 :=
      CFSGSmallLinearSimpleOuterSixtyFour.cardFactors_le_five_of_le_thirtySix
        Nat.card_pos.ne' (hquot.trans hout)
    rw [T.abelianLength_eq]
    exact (actualChiefSeriesAbelianLength_le_quotient_cardFactors T.chief E hE.2.1 hnc
      (fun N hN hnN => by
        letI : N.Normal := hN
        exact CFSGSelfCentralizingMinimalNormal.le_every_nontrivial_normal
          E hE hC N hnN)).trans (hsmall.trans (by decide : 5 ≤ 14))
  · exact hsmall

end SymmetricSubgroupAsymptotics.CFSGPrimitiveBinarySixTraceBound
