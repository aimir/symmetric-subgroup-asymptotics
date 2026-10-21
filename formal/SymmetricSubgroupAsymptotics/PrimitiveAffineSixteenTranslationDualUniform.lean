import SymmetricSubgroupAsymptotics.ActualWreathOriginalKernelDualUniform
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationLayerSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixteenCoordinateAction
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof

/-! Uniform dual capacity of the actual correlated translation kernel in
an affine16 block system. Only the proved refined induced-module theorem
is used; no soluble complement locator or minimal-constituent census occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

/-- Re-express the characteristic as literal2 while retaining the SAME
regular subgroup and SAME original action. -/
def sixteenBinaryProfile (hr : Nat.card block.Fibre=16) :
    PrimitiveAffineProfile block.Component block.Fibre where
  p := 2
  p_prime := by decide
  V := P.V
  V_normal := P.V_normal
  V_pgroup := by
    rw [←(P.degreeSixteen_prime_dimension block.component_preprimitive (origin block) hr).1]
    exact P.V_pgroup
  regular := P.regular

/-- The exact quotient module, uniformly over all its subrepresentations,
costs at most two generators per actual block. -/
theorem sixteen_translation_dual_uniform
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre=16) :
    let Q := sixteenBinaryProfile block P hr
    let S := initialState hTraceyPerm block
    let C := localTranslationChart block Q
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.E S (localMap block Q) C).quotientRepresentation.ρ.dual
      (2*Fintype.card block.Points) := by
  let Q := sixteenBinaryProfile block P hr
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block Q
  let D := ActualWreathAffineCapacity.refinedCapacityData S
    (localMap block Q) C traceyRefinedInducedModuleInput_proved
    (by simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2) block.base
  have hd : Module.finrank (ZMod C.p) C.V=4 := by
    simpa only [C,localTranslationChart,chart,PrimitiveAffineProfile.ElementaryChart.d]
      using (Q.degreeSixteen_prime_dimension block.component_preprimitive (origin block) hr).2
  have hhalf := D.bounds.half
  change (D.H : ℝ) ≤ (Module.finrank (ZMod C.p) C.V : ℝ)*Fintype.card block.Points/2 at hhalf
  rw [hd] at hhalf
  have hH : D.H ≤ 2*Fintype.card block.Points := by
    have hR : (D.H : ℝ) ≤ ((2*Fintype.card block.Points : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hR
  exact uniformSubrepresentationGeneratorBound_mono _
    (ActualWreathAffineCapacity.originalKernel_dual_uniform S (localMap block Q) C block.base D) hH

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
