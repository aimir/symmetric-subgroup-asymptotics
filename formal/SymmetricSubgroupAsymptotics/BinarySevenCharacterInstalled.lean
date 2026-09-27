import SymmetricSubgroupAsymptotics.BinaryPermutationClassBound
import SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenBoundary

/-!
# Installing the actual binary class theorem in the new character envelope

The finite-base/block-induction class theorem supplies the specific integer
input required by the separate 5^(2/7) interface. Consequently these original
epimorphism, survival and power-boundary physical bounds have no class-count
premise. This neither proves nor modifies the distinct old 38/25 input.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinarySevenCharacterInstalled

theorem class_input : BinarySevenPermutationClassInput := by
  intro b P hP
  simpa only [Nat.card_fin] using
    BinaryPermutationClassBound.literal_class_card_pow_seven_le (Fin b) P hP

/-- Arbitrary exterior, actual binary target and original automorphism factor. -/
theorem original_envelope {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q):ℝ) ≤ (Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binarySevenCharacterSlope
        (Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)))*(b:ℝ)) :=
  binarySeven_groupEpimorphism_original_envelope class_input hQ b J

theorem survival_envelope {Q : Type} [Group Q] [Finite Q] {w : ℕ}
    (C : BinarySevenCharacterCriterion Q w) (hQ : IsPGroup 2 Q)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f}:ℝ) ≤ (Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binarySevenCharacterSlope C.dimension*(b:ℝ)) :=
  C.survival_envelope class_input hQ b J S

section PowerBoundary

open BinaryTransitivePowerSevenBoundary

variable {h : ℕ} (k : ℕ) (hk : 4≤k)
    (U : Subgroup (Equiv.Perm (Fin (2*h))))
    [MulAction.IsPretransitive U (Fin (2*h))]
    (hdegree : 2*h=2^k) (hcard : Nat.card U≤2^(2^(k-1)))

/-- Complete original-normal first-moment physical bound. The faithful
transitive action and source order are the only structural acceptance data. -/
theorem powerBoundary_direct_physical_bound (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)):ℝ)/
      exactBenchmark (b+2*h) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        fusionDirectKernel b h ((selectionOfDegree k hk U hdegree hcard).prefixDegree N)
          ((selectionOfDegree k hk U hdegree hcard).liftConstant N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))):ℝ)
          ((selectionOfDegree k hk U hdegree hcard).gapParameter N)*
          ((subgroupCount (b+(selectionOfDegree k hk U hdegree hcard).prefixDegree N):ℝ)/
            exactBenchmark (b+(selectionOfDegree k hk U hdegree hcard).prefixDegree N)) :=
  BinaryTransitivePowerSevenBoundary.direct_physical_bound k hk U hdegree hcard
    class_input hU b P hP

end PowerBoundary
end SymmetricSubgroupAsymptotics.BinarySevenCharacterInstalled

end
