import SymmetricSubgroupAsymptotics.BinarySevenCharacterEnvelope
import SymmetricSubgroupAsymptotics.BinaryTargetOrderFusion
import SymmetricSubgroupAsymptotics.FusionDirectPhysicalUnion

/-!
# Direct original-axis fusion with the new binary class rate

Every literal original normal receives either its existing target-order
certificate or a separate 5^(2/7) character certificate. The latter keeps
the original target automorphism factor, marker zero and moment weight one.
All choices precede the exterior group. The class premise is specifically
the actual binary permutation theorem, never the old nilpotent 38/25 input.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

abbrev BinaryOrderSevenCharacterCertificate {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal] :=
  BinaryTargetOrderCertificate U N ⊕ BinarySevenCharacterCriterion (U⧸N) w

namespace BinaryOrderSevenCharacterCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (C : BinaryOrderSevenCharacterCertificate U N)

def prefixDegree : ℕ := match C with
  | .inl B => B.prefixDegree
  | .inr _ => 0

def markerHalf : ℕ := match C with
  | .inl _ => Nat.log 2 (Nat.card (U⧸N))
  | .inr _ => 0

def liftConstant : ℝ := match C with
  | .inl B => B.liftConstant
  | .inr _ => Nat.card ((U⧸N)≃*(U⧸N))

def gapParameter : ℝ := match C with
  | .inl B => B.gapParameter
  | .inr B => ((w:ℝ)-8*binarySevenCharacterSlope B.dimension)/16

def momentWeight (J : Type*) [Group J] : ℝ := match C with
  | .inl B => B.momentWeight J
  | .inr _ => 1

theorem prefixDegree_eq_two_mul : C.prefixDegree = 2*C.markerHalf := by
  cases C <;> rfl

theorem prefixDegree_lt (hw : 0<w) : C.prefixDegree < w := by
  cases C with
  | inl B => exact B.gap
  | inr B => exact hw

theorem liftConstant_nonneg : 0 ≤ C.liftConstant := by
  cases C with
  | inl B => exact B.liftConstant_nonneg
  | inr B => exact Nat.cast_nonneg _

theorem gapParameter_pos : 0 < C.gapParameter := by
  cases C with
  | inl B => exact B.gapParameter_pos
  | inr B =>
      have h := B.slope_gap
      change 0 < ((w:ℝ)-8*binarySevenCharacterSlope B.dimension)/16
      linarith

/-- The new character branch has exact same-source moments, including q=0. -/
theorem character_moment_eq (B : BinarySevenCharacterCriterion (U⧸N) w) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      momentWeight (.inr B : BinaryOrderSevenCharacterCertificate U N) J^q) =
        (subgroupCount b : ℝ) := by
  simp [momentWeight, subgroupCount, Nat.card_eq_fintype_card]

theorem moment_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight J^q) ≤
      (subgroupCount (b+q*C.prefixDegree) : ℝ) := by
  cases C with
  | inl B => exact B.prefixDegree_moment_le b q
  | inr B =>
      rw [character_moment_eq]
      simp only [prefixDegree, mul_zero, add_zero]
      exact le_rfl

end BinaryOrderSevenCharacterCertificate

namespace BinaryOrderSevenCharacterCertificate

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    {N : Subgroup U} [N.Normal]

theorem character_localFactor_eq
    (B : BinarySevenCharacterCriterion (U⧸N) (2*h)) (b : ℕ) :
    fusionLocalFactor b h
      (prefixDegree (.inr B : BinaryOrderSevenCharacterCertificate U N))
      (liftConstant (.inr B : BinaryOrderSevenCharacterCertificate U N))
      (gapParameter (.inr B : BinaryOrderSevenCharacterCertificate U N)) =
        (Nat.card ((U⧸N)≃*(U⧸N)):ℝ)*
          (2:ℝ)^(binarySevenCharacterSlope B.dimension*(b:ℝ)) := by
  simp only [prefixDegree, liftConstant, gapParameter, fusionLocalFactor,
    Nat.cast_zero, sub_zero]
  congr 1
  congr 1
  ring

theorem original_envelope (C : BinaryOrderSevenCharacterCertificate U N)
    (hclass : BinarySevenPermutationClassInput) (hU : IsPGroup 2 U) {b : ℕ}
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N,inferInstance⟩ J ≤
      fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  cases C with
  | inl B => exact B.original_survivingEpiCount_le_localFactor hU P J
  | inr B =>
      rw [character_localFactor_eq]
      simp only [momentWeight, mul_one]
      exact binarySevenCharacter_physicalAxis_envelope hclass U hU P
        ⟨N,inferInstance⟩ B J

end BinaryOrderSevenCharacterCertificate

/-- Complete selection, with no excluded original normal. -/
abbrev BinaryOrderSevenCharacterSelection {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) :=
  ∀ N : {N : Subgroup U // N.Normal}, BinaryOrderSevenCharacterCertificate U N.1

namespace BinaryOrderSevenCharacterSelection

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    (C : BinaryOrderSevenCharacterSelection U)

def prefixDegree (N : {N : Subgroup U // N.Normal}) : ℕ := (C N).prefixDegree
def markerHalf (N : {N : Subgroup U // N.Normal}) : ℕ := (C N).markerHalf
def liftConstant (N : {N : Subgroup U // N.Normal}) : ℝ := (C N).liftConstant
def gapParameter (N : {N : Subgroup U // N.Normal}) : ℝ := (C N).gapParameter
def momentWeight (N : {N : Subgroup U // N.Normal}) (J : Type*) [Group J] : ℝ :=
  (C N).momentWeight J

theorem liftConstant_nonneg (N : {N : Subgroup U // N.Normal}) :
    0 ≤ C.liftConstant N := (C N).liftConstant_nonneg

theorem gapParameter_pos (N : {N : Subgroup U // N.Normal}) :
    0 < C.gapParameter N := (C N).gapParameter_pos

theorem moment_le (N : {N : Subgroup U // N.Normal}) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight N J^q) ≤
      (subgroupCount (b+q*C.prefixDegree N) : ℝ) := (C N).moment_le b q

end BinaryOrderSevenCharacterSelection

namespace BinaryOrderSevenCharacterSelection

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    (C : BinaryOrderSevenCharacterSelection U)

theorem original_envelope (hclass : BinarySevenPermutationClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal}) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b h (C.prefixDegree N) (C.liftConstant N) (C.gapParameter N)*
        C.momentWeight N J := (C N).original_envelope hclass hU P J

/-- The actual original normalizer divides the complete first-moment sum. -/
theorem direct_physical_bound (hclass : BinarySevenPermutationClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)):ℝ)/
      exactBenchmark (b+2*h) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        fusionDirectKernel b h (C.prefixDegree N) (C.liftConstant N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))):ℝ)
          (C.gapParameter N)*
            ((subgroupCount (b+C.prefixDegree N):ℝ)/exactBenchmark (b+C.prefixDegree N)) :=
  fusionPhysical_direct_bound U b P hP C.prefixDegree C.liftConstant C.gapParameter
    (fun N J => C.momentWeight N J) C.liftConstant_nonneg
    (C.original_envelope hclass hU b P)
    (fun N => by simpa only [pow_one, one_mul] using C.moment_le N b 1)

end BinaryOrderSevenCharacterSelection

end SymmetricSubgroupAsymptotics

end
