import SymmetricSubgroupAsymptotics.PrimitiveAffineBottomFibre
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoBinaryKernelAnchor

/-!
# Schur lifts for the degree-two pair rows

The pair-top module tables bound a Schur capacity, not the dimension of the
whole elementary pair kernel.  This distinction matters already for the
full wreath extension: the kernel can have dimension equal to the number of
pairs while its natural permutation module has small Schur capacity.

This file gives the reusable extension theorem needed by those tables.  An
ordinary-character envelope on the literal top is lifted through the actual
elementary binary extension.  The general Schur lift bound costs
`capacity / 2` in the exponent because the source is a permutation group.
That is no larger than the catalogue's conservative
`capacity * log_2(38/25)` relative allowance.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeTwoPairRelativeQuotientEnvelope

/-- Transport a fixed-target epimorphism envelope across an exact target
equivalence. -/
noncomputable def ofTargetEquiv
    {B C : Type} [Group B] [Finite B] [Group C] [Finite C]
    {profile : DegreeTwoPairRelativeProfile}
    (top : DegreeTwoPairRelativeQuotientEnvelope C profile)
    (e : B ≃* C) :
    DegreeTwoPairRelativeQuotientEnvelope B profile where
  coefficient := top.coefficient
  coefficient_nonneg := top.coefficient_nonneg
  bound := by
    intro b J
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact top.bound b J

end DegreeTwoPairRelativeQuotientEnvelope

/-- The Schur exponent `1/2` is strictly below the binary relative exponent
used by the pair catalogues. -/
theorem half_le_logb_two_thirtyEight_div_twentyFive :
    (1 : ℝ) / 2 ≤ Real.logb 2 (38 / 25) := by
  have hp : (2 : ℝ) ^ (1 : ℕ) < (38 / 25 : ℝ) ^ (2 : ℕ) := by
    norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ (1 : ℕ)) hp
  simp only [Real.logb_pow, Nat.cast_one, one_mul,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    Nat.cast_ofNat] at hlog
  linarith

/-- Lift an ordinary top envelope through an actual elementary binary
extension whose kernel representation has bounded Schur capacity.

The translation and first-cohomology factors are retained in the fixed
target coefficient.  The source-dependent part uses the proved permutation
rank bound in `fusionEpimorphism_survival_card_le_schur_of_permutation_source`.
No dimension bound on the elementary kernel is assumed. -/
noncomputable def degreeTwoPairSchurLiftEnvelope
    {Q B V : Type} [Group Q] [Finite Q] [Group B] [Finite B]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (pi : Q →* B) (hpi : Function.Surjective pi)
    (M : Rep (ZMod 2) B) (E : OriginalKernelModuleChart pi M)
    (ordinary relative : ℕ)
    (top : DegreeTwoPairRelativeQuotientEnvelope B
      (degreeTwoPairGeneralProfile ordinary))
    (capacity_le : representationSchurCapacity M.ρ ≤ relative) :
    DegreeTwoPairRelativeQuotientEnvelope Q
      (degreeTwoPairOrdinaryRelativeProfile ordinary relative) where
  coefficient := top.coefficient *
    ((Nat.card M : ℝ) * Nat.card (groupCohomology.H1 M))
  coefficient_nonneg := mul_nonneg top.coefficient_nonneg (by positivity)
  bound := by
    intro b J
    let extensionConstant : ℝ :=
      (Nat.card M : ℝ) * Nat.card (groupCohomology.H1 M)
    have hraw := fusionEpimorphism_survival_card_le_schur_of_permutation_source
      2 J pi hpi M E (fun _ ↦ True)
    have hcard : Nat.card {f : GroupEpimorphism J Q // True} =
        Nat.card (GroupEpimorphism J Q) := by simp
    rw [hcard] at hraw
    have hraw' : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        Nat.card (GroupEpimorphism J B) *
          (extensionConstant *
            (2 : ℝ) ^
              (representationSchurCapacity M.ρ * ((b : ℝ) / 2))) := by
      simpa only [extensionConstant] using hraw
    have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
    have hrelative : 0 ≤ (relative : ℝ) := Nat.cast_nonneg relative
    have hlog := half_le_logb_two_thirtyEight_div_twentyFive
    have hexponent :
        representationSchurCapacity M.ρ * ((b : ℝ) / 2) ≤
          (relative : ℝ) * Real.logb 2 (38 / 25) * b := by
      have hcap : representationSchurCapacity M.ρ ≤ (relative : ℝ) :=
        capacity_le
      calc
        representationSchurCapacity M.ρ * ((b : ℝ) / 2) ≤
            (relative : ℝ) * ((b : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hcap (by positivity)
        _ ≤ (relative : ℝ) * Real.logb 2 (38 / 25) * b := by
          nlinarith
    have hschur :
        (2 : ℝ) ^
            (representationSchurCapacity M.ρ * ((b : ℝ) / 2)) ≤
          (2 : ℝ) ^
            ((relative : ℝ) * Real.logb 2 (38 / 25) * b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    calc
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
          Nat.card (GroupEpimorphism J B) *
            (extensionConstant *
              (2 : ℝ) ^
                (representationSchurCapacity M.ρ * ((b : ℝ) / 2))) :=
        hraw'
      _ ≤ (top.coefficient *
            (2 : ℝ) ^
              ((degreeTwoPairGeneralProfile ordinary).slope * b)) *
            (extensionConstant *
              (2 : ℝ) ^
                ((relative : ℝ) * Real.logb 2 (38 / 25) * b)) := by
        apply mul_le_mul
        · exact top.bound b J
        · exact mul_le_mul_of_nonneg_left hschur (by positivity)
        · positivity
        · positivity
      _ = (top.coefficient * extensionConstant) *
            (2 : ℝ) ^
              ((degreeTwoPairOrdinaryRelativeProfile ordinary relative).slope * b) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        unfold DegreeTwoPairRelativeProfile.slope
          degreeTwoPairGeneralProfile degreeTwoPairOrdinaryRelativeProfile
        ring

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
