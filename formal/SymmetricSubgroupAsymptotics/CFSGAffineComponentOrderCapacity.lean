import SymmetricSubgroupAsymptotics.CFSGAffineComponentIntegerMargin

/-! The actual imprimitive component tower can be paid directly from its
original chief-series order charge. The unbounded range needs neither a
primitive composition-length assumption nor a finite catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (hHalf : TraceyAffineHalfInducedModuleInput) (hLog : TraceyAffineInducedModuleInput)
    (hRefined : TraceyRefinedInducedModuleInput) (hPerm : TraceyPermutationGeneratorInput)
    (block : OriginalMinimalBlock (A:=preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem actual_trace_abelianLength_le_logSquare :
    (ComponentSource.tower hHalf hLog hRefined hPerm block P).abelianLength ≤
      (Nat.log2 (Nat.card block.Fibre)+1)^2 := by
  letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let T := ComponentSource.trace hHalf hLog hRefined hPerm block P
  rw [show ComponentSource.tower hHalf hLog hRefined hPerm block P = T.tower from rfl,
    T.abelianLength_eq]
  exact P.chiefAbelianLength_le_logSquare block.component_preprimitive T.chief

namespace ComponentSource

def of_integer_order_charge (c : ℕ)
    (hc : (tower hHalf hLog hRefined hPerm block P).abelianLength ≤ c)
    (hbudget : 54272*c+38400 ≤ 25575*Nat.card block.Fibre) :
    ComponentSource hHalf hLog hRefined hPerm block P where
  margin := by
    letI : Nontrivial block.Fibre := Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
    let T := tower hHalf hLog hRefined hPerm block P
    have hv : T.envelope.v = Nat.card block.Points := by
      simpa only [Fintype.card_eq_nat_card] using ActualWreathCompressionTower.envelope_v T
    change preE7CharacterRho*(w:ℝ) ≤ ((evenWidth w:ℝ)-(T.envelope.v:ℝ))/8-T.envelope.eta
    rw [hv]
    apply primitiveAffine_margin_of_integer_charge (Nat.card block.Fibre)
      (Nat.card block.Points) w c block.degrees_ge_two.2 (width_eq block) hbudget
    have hT := ActualWreathCompressionTower.envelope_eta_le_abelianLength T
    have hfac : 0 ≤ fixedTargetCompositionGamma*((Nat.card block.Points:ℝ)/2) :=
      mul_nonneg
        (div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num))
        (by positivity)
    have hT' : T.envelope.eta ≤ fixedTargetCompositionGamma*
        ((Nat.card block.Points:ℝ)/2)*T.abelianLength := by
      simpa only [Fintype.card_eq_nat_card] using hT
    exact hT'.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hfac)

def of_localDegree_ge_oneThousandTwentyFour_order
    (hr : 1024 ≤ Nat.card block.Fibre) :
    ComponentSource hHalf hLog hRefined hPerm block P := by
  let n := Nat.log2 (Nat.card block.Fibre)+1
  apply of_integer_order_charge hHalf hLog hRefined hPerm block P (n^2)
    (actual_trace_abelianLength_le_logSquare hHalf hLog hRefined hPerm block P)
  have hq := CFSGPrimitiveTernaryTailNumerics.quadratic_log_tail hr
  change 20*(n^2+2*n)<3*Nat.card block.Fibre at hq
  nlinarith

end ComponentSource
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
