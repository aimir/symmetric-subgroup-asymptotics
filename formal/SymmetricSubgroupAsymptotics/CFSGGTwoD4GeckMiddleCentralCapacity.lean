import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFullCentralLine
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedCommutators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup
import SymmetricSubgroupAsymptotics.FinitePGroupProperSubgroupCardinality

/-! Capacity of the literal full central intersection. The proof embeds
the same fixed radical into the actual positive p-group, so no exponent
three or additive coordinate chart on its q^3 centre is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralCapacity
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleCentralExtensionData
open CFSGGTwoD4GeckMiddleFullCentralLine CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinatePositivePGroup
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

variable (K : Type) [Field K] [Finite K]

theorem fixedMiddle_isPGroup (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (fixedMiddle K) := by
  let R := rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K false
  let f : fixedMiddle K →* R :=
    { toFun := fun u => ⟨u.val,
        CFSGTrialityGeckMiddleFixedCommutators.middle_le_positive K u.property.1⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    exact congrArg (fun z : R => z.val) he
  exact (rootGroup_isPGroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    Index K p false).of_injective f hf

theorem central_intersection_mul_three_le [CharP K 3] (hcard : 4 ≤ Nat.card K)
    (J : Subgroup (fixedMiddle K))
    (hJ : central K (Multiplicative.ofAdd (1 : K)) ∉ J) :
    3*Nat.card (J.comap (Subgroup.center (fixedMiddle K)).subtype) ≤ Nat.card K^3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C := J.comap (Subgroup.center (fixedMiddle K)).subtype
  have hC : C ≠ ⊤ := by
    intro ht
    apply hJ
    have hmem : highInCenter K hcard (Multiplicative.ofAdd (1 : K)) ∈ C := by
      rw [ht]
      trivial
    exact hmem
  have hc := FinitePGroupProperSubgroupCardinality.prime_mul_card_le 3
    ((fixedMiddle_isPGroup K 3).to_subgroup (Subgroup.center (fixedMiddle K))) C hC
  rw [center_card K hcard] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralCapacity
