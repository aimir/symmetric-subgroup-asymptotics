import SymmetricSubgroupAsymptotics.BinaryElementaryActualComparatorSource
import SymmetricSubgroupAsymptotics.ActualWreathOriginalKernelDualUniform
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreSource
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof

/-! Actual zero-ternary-core degree4/count16 actions have an elementary
binary kernel and the SAME faithful16-point quotient. Refined binomial
capacity12 supplies a complete cold-rank source, retaining every original
normal denominator and bypassing the stronger finite-frame rank split. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

def degreeFourBinaryProfile (hr : Nat.card block.Fibre=4) :
    PrimitiveAffineProfile block.Component block.Fibre where
  p := 2
  p_prime := by decide
  V := P.V
  V_normal := P.V_normal
  V_pgroup := by rw [←(degreeFour_translationDimension block P hr).1]; exact P.V_pgroup
  regular := P.regular

/-- The exact quotient dual costs12, by local dimension2 and block index16. -/
theorem degreeFourSixteen_translation_dual_uniform
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=4) (hs : Nat.card block.Points=16) :
    let Q := degreeFourBinaryProfile block P hr
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block Q
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.E S (localMap block Q) C).quotientRepresentation.ρ.dual 12 := by
  let Q := degreeFourBinaryProfile block P hr
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block Q
  let D := ActualWreathAffineCapacity.refinedCapacityData S (localMap block Q) C
    traceyRefinedInducedModuleInput_proved
    (by simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2) block.base
  have hd : Module.finrank (ZMod C.p) C.V=2 := by
    simpa only [C,localTranslationChart,chart,PrimitiveAffineProfile.ElementaryChart.d]
      using (degreeFour_translationDimension block Q hr).2
  have hc : Fintype.card block.Points=16 := by simpa only [Fintype.card_eq_nat_card] using hs
  have hb := D.bounds.primePower 2 4 Nat.prime_two (by decide) (by rw [hc]; norm_num)
  change (D.H : ℝ) ≤ (Module.finrank (ZMod C.p) C.V : ℝ)*
    (Fintype.card block.Points : ℝ)*(Nat.choose 4 (4/2) : ℝ)/(2 : ℝ)^4 at hb
  rw [hd,hc] at hb
  have hH : D.H ≤ 12 := by norm_num [Nat.choose] at hb; exact_mod_cast hb
  exact uniformSubrepresentationGeneratorBound_mono _
    (ActualWreathAffineCapacity.originalKernel_dual_uniform S (localMap block Q) C block.base D) hH

/-- The actual quotient embeds inS16; the actual kernel has size ≤ 4^16. -/
theorem degreeFourSixteen_zeroCore_order_budgets
    (hr : Nat.card block.Fibre=4) (hs : Nat.card block.Points=16)
    (hzero : degreeFourTernaryCore block P=⊥) :
    Nat.card (preE7NonPairAction w U) ≤ 2^77 ∧
      Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2^45 := by
  have hQ := Nat.card_le_card_of_injective
    (degreeFourZeroCoreTopAction block P)
    (degreeFourZeroCoreTopAction_injective block P hr hzero)
  have hperm : Nat.card (Equiv.Perm (Fin (Nat.card block.Points)))=Nat.factorial 16 := by
    simp only [Nat.card_perm,Nat.card_fin,hs]
  have hQ' : Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2^45 :=
    (hQ.trans_eq hperm).trans (by norm_num)
  have hE : Nat.card (E block P) ≤ 2^32 := by
    have hh := translationIntersection_card_le block P
    simpa only [hr,hs,show (4 : ℕ)^16=2^32 by norm_num] using hh
  refine ⟨?_,hQ'⟩
  rw [←(E block P).card_mul_index,Subgroup.index_eq_card]
  exact (Nat.mul_le_mul hE hQ').trans_eq (by rw [←pow_add])

/-- Full actual physical source data; the stronger old head ≤ 2 plus
coinvariant ≤ 8 classification is not used or asserted. -/
def degreeFourSixteenZeroCoreColdData
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=4) (hs : Nat.card block.Points=16)
    (hzero : degreeFourTernaryCore block P=⊥) :
    PreE7DegreeTwoPairSummedSource w U := by
  let Q := degreeFourBinaryProfile block P hr
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block Q
  let pi := QuotientGroup.mk' (E block Q)
  let A := (ActualWreathAffineCapacity.E S (localMap block Q) C).quotientRepresentation
  let EC := ActualWreathAffineCapacity.originalChart S (localMap block Q) C
  have hzeroQ : degreeFourTernaryCore block Q=⊥ := hzero
  have caps := degreeFourSixteen_zeroCore_order_budgets block Q hr hs hzeroQ
  exact BinaryElementaryActualComparatorSource.data pi (QuotientGroup.mk'_surjective (E block Q))
    A EC (degreeFourSixteen_translation_dual_uniform block P hTraceyPerm hr hs)
    77 45 caps.1 caps.2 (Nat.card block.Points)
    (degreeFourZeroCoreTopAction block Q)
    (degreeFourZeroCoreTopAction_injective block Q hr hzeroQ)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
