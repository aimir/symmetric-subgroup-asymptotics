import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters
import Mathlib.GroupTheory.Index

/-! The eight actual cube parameters cover the genuine quotient R/Z.
The previously proved injection, actual radical order, and highest-root
parameter order give surjectivity. Consequently the literal middle first
layer has exactly the highest root subgroup as its kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEquiv
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4MiddleCube CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleRadicalCardinality
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

theorem highestInMiddle_card (K : Type) [Field K] :
    Nat.card (highestInMiddle K) = Nat.card K := by
  calc
    Nat.card (highestInMiddle K) = Nat.card (highestLine K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (highest_le_middle K)).toEquiv
    _ = Nat.card K :=
      CFSGNormTwoCoordinateAllRootParameters.rootSubgroup_card A hd hs hp ho K (longRoot 2)

theorem middleQuotient_card (K : Type) [Field K] [Finite K] :
    Nat.card (MiddleQuotient K) = Nat.card K ^ 8 := by
  have hcard := (highestInMiddle K).card_mul_index
  rw [Subgroup.index_eq_card, highestInMiddle_card, middleRadical_card] at hcard
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K))
  calc
    Nat.card K * Nat.card (MiddleQuotient K) = Nat.card K ^ 9 := hcard
    _ = Nat.card K * Nat.card K ^ 8 := by rw [← pow_succ']

theorem cubeProduct_surjective (K : Type) [Field K] [Finite K] :
    Function.Surjective (cubeProductHom K) := by
  have hcard : Nat.card (MiddleQuotient K) ≤ Nat.card (Cube → Multiplicative K) := by
    rw [middleQuotient_card, Nat.card_fun, Nat.card_congr
      (Multiplicative.toAdd : Multiplicative K ≃ K)]
    have hc : Nat.card Cube = 8 := by simp [Cube]
    rw [hc]
  exact ((cubeProduct_injective K).bijective_of_nat_card_le hcard).surjective

def cubeEquiv (K : Type) [Field K] [Finite K] :
    (Cube → Multiplicative K) ≃* MiddleQuotient K :=
  MulEquiv.ofBijective (cubeProductHom K) ⟨cubeProduct_injective K, cubeProduct_surjective K⟩

theorem quotientFirstLayer_injective (K : Type) [Field K] [Finite K] :
    Function.Injective (quotientFirstLayerHom K) := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := cubeProduct_surjective K x
  obtain ⟨d, rfl⟩ := cubeProduct_surjective K y
  have h := congrArg Multiplicative.toAdd hxy
  rw [cubeProduct_firstLayer, cubeProduct_firstLayer] at h
  have hcoeff := cube_coefficients_unique K (fun a => (c a).toAdd) (fun a => (d a).toAdd) h
  have hcd : c = d := by
    funext a
    exact congrArg Multiplicative.ofAdd (congrFun hcoeff a)
  rw [hcd]

theorem firstLayer_kernel_eq_highest (K : Type) [Field K] [Finite K] :
    (middleFirstLayerHom K).ker = highestInMiddle K := by
  apply le_antisymm _ (highest_le_firstLayer_kernel K)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply quotientFirstLayer_injective K
  rw [map_one]
  change middleFirstLayerHom K x = 1
  exact hx

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEquiv
