import SymmetricSubgroupAsymptotics.BinaryTargetOrderFusion
import SymmetricSubgroupAsymptotics.BinaryCharacterFusion

/-!
# Complete original-axis order or character fusion

Each literal original normal receives an order or character certificate,
chosen before the exterior degree, subgroup and survival condition. The
character branch has zero prefix degree and constant moment weight one.
Its exact original automorphism factor and named conjugacy-class input are
retained. Both branches use the same original-normalizer physical sum.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

/-- Both alternatives concern the same literal original group and normal. -/
abbrev BinaryOrderCharacterCertificate {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal] :=
  BinaryTargetOrderCertificate U N ⊕ BinaryNormalCharacterCriterion (U ⧸ N) w

namespace BinaryOrderCharacterCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (C : BinaryOrderCharacterCertificate U N)

def prefixDegree : ℕ :=
  match C with
  | .inl B => B.prefixDegree
  | .inr _ => 0

def liftConstant : ℝ :=
  match C with
  | .inl B => B.liftConstant
  | .inr _ => Nat.card ((U ⧸ N) ≃* (U ⧸ N))

def gapParameter : ℝ :=
  match C with
  | .inl B => B.gapParameter
  | .inr B => ((w : ℝ) - 8 * binaryCharacterSlope B.dimension) / 16

def momentWeight (J : Type*) [Group J] : ℝ :=
  match C with
  | .inl B => B.momentWeight J
  | .inr _ => 1

theorem liftConstant_nonneg : 0 ≤ C.liftConstant := by
  cases C with
  | inl B => exact B.liftConstant_nonneg
  | inr B =>
      change 0 ≤ (Nat.card ((U ⧸ N) ≃* (U ⧸ N)) : ℝ)
      positivity

theorem gapParameter_pos : 0 < C.gapParameter := by
  cases C with
  | inl B => exact B.gapParameter_pos
  | inr B =>
      have h := B.slope_gap
      change 0 < ((w : ℝ) - 8 * binaryCharacterSlope B.dimension) / 16
      linarith

theorem momentWeight_nonneg (J : Type*) [Group J] : 0 ≤ C.momentWeight J := by
  cases C with
  | inl B => exact B.momentWeight_nonneg J
  | inr B => exact zero_le_one

/-- Exact zero-prefix moment identity on the character branch. -/
theorem character_moment_eq
    (B : BinaryNormalCharacterCriterion (U ⧸ N) w) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
      momentWeight (.inr B : BinaryOrderCharacterCertificate U N) J ^ q) =
      (subgroupCount b : ℝ) := by
  simp [momentWeight, subgroupCount, Nat.card_eq_fintype_card]

/-- Character moments are exactly the original subgroup count, including
moment zero; there is no auxiliary cover or extra character marker. -/
theorem prefixDegree_moment_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight J ^ q) ≤
      (subgroupCount (b + q * C.prefixDegree) : ℝ) := by
  cases C with
  | inl B => exact B.prefixDegree_moment_le b q
  | inr B =>
      simp [momentWeight, prefixDegree, subgroupCount, Nat.card_eq_fintype_card]
      exact le_rfl

end BinaryOrderCharacterCertificate

namespace BinaryOrderCharacterCertificate

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    {N : Subgroup U} [N.Normal]

/-- The numerical local factor is exactly the existing same-source
character envelope, with its original target automorphism cardinality. -/
theorem character_localFactor_eq
    (B : BinaryNormalCharacterCriterion (U ⧸ N) (2*h)) (b : ℕ) :
    fusionLocalFactor b h
      (prefixDegree (.inr B : BinaryOrderCharacterCertificate U N))
      (liftConstant (.inr B : BinaryOrderCharacterCertificate U N))
      (gapParameter (.inr B : BinaryOrderCharacterCertificate U N)) =
      (Nat.card ((U ⧸ N) ≃* (U ⧸ N)) : ℝ) *
        (2 : ℝ) ^ (binaryCharacterSlope B.dimension * (b : ℝ)) := by
  simp only [prefixDegree, liftConstant, gapParameter, fusionLocalFactor,
    Nat.cast_zero, sub_zero]
  congr 1
  congr 1
  ring

theorem original_survivingEpiCount_le_localFactor
    (C : BinaryOrderCharacterCertificate U N)
    (hMaroti : NilpotentConjugacyClassInput) (hU : IsPGroup 2 U) {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  cases C with
  | inl B => exact B.original_survivingEpiCount_le_localFactor hU P J
  | inr B =>
      rw [character_localFactor_eq]
      simp only [momentWeight, mul_one]
      exact binaryCharacter_physicalAxis_envelope hMaroti U hU P
        ⟨N, inferInstance⟩ B J

end BinaryOrderCharacterCertificate

/-- Complete selection on all original normal axes, with no excluded case.
It cannot depend on the exterior group, degree or hot/cold test. -/
abbrev BinaryOrderCharacterSelection {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) :=
  ∀ N : {N : Subgroup U // N.Normal}, BinaryOrderCharacterCertificate U N.1

namespace BinaryOrderCharacterSelection

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    (C : BinaryOrderCharacterSelection U)

def prefixDegree (N : {N : Subgroup U // N.Normal}) : ℕ := (C N).prefixDegree

def liftConstant (N : {N : Subgroup U // N.Normal}) : ℝ := (C N).liftConstant

def gapParameter (N : {N : Subgroup U // N.Normal}) : ℝ := (C N).gapParameter

def momentWeight (N : {N : Subgroup U // N.Normal}) (J : Type*) [Group J] : ℝ :=
  (C N).momentWeight J

theorem liftConstant_nonneg (N : {N : Subgroup U // N.Normal}) :
    0 ≤ C.liftConstant N := (C N).liftConstant_nonneg

theorem gapParameter_pos (N : {N : Subgroup U // N.Normal}) :
    0 < C.gapParameter N := (C N).gapParameter_pos

theorem momentWeight_nonneg (N : {N : Subgroup U // N.Normal})
    (J : Type*) [Group J] : 0 ≤ C.momentWeight N J := (C N).momentWeight_nonneg J

theorem momentWeight_moment_le (N : {N : Subgroup U // N.Normal}) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight N J ^ q) ≤
      (subgroupCount (b + q * C.prefixDegree N) : ℝ) :=
  (C N).prefixDegree_moment_le b q

end BinaryOrderCharacterSelection

namespace BinaryOrderCharacterSelection

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    (C : BinaryOrderCharacterSelection U)

/-- Every actual surviving original map receives the selected envelope.
No naturality of the certificate choice itself is required. -/
theorem original_envelope (hMaroti : NilpotentConjugacyClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal}) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b h (C.prefixDegree N) (C.liftConstant N) (C.gapParameter N) *
        C.momentWeight N J :=
  (C N).original_survivingEpiCount_le_localFactor hMaroti hU P J

/-- The original normalizer divides the complete original-axis sum.
Neither quotient automorphisms nor marker groups replace this divisor. -/
theorem physical_kernel_bound (hMaroti : NilpotentConjugacyClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
      exactBenchmark (b+2*h) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        (fusionMenuHotKernel (fun n => (subgroupCount n : ℝ)) b h (C.prefixDegree N)
          (C.liftConstant N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))) : ℝ)
          (C.gapParameter N) +
        fusionColdKernel b h (C.liftConstant N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))) : ℝ)
          (16*C.gapParameter N) * ((subgroupCount b : ℝ)/exactBenchmark b)) :=
  fusionPhysical_kernel_bound U b P hP C.prefixDegree C.liftConstant C.gapParameter
    (fun N J => C.momentWeight N J) C.liftConstant_nonneg
    (fun N => (C.gapParameter_pos N).le) (fun N J => C.momentWeight_nonneg N J)
    (C.original_envelope hMaroti hU b P)
    (fun N q _hq => C.momentWeight_moment_le N b q)

end BinaryOrderCharacterSelection

section Menu

variable {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))
    (C : ∀ i, BinaryOrderCharacterSelection (U i))

/-- A finite literal cover gives the original-weight recurrence from the
proved order/character envelopes. Coverage and family naturality remain
explicit, as does the named class-count input. No axes are excluded. -/
theorem binaryOrderCharacterSelection_recurrence
    (hMaroti : NilpotentConjugacyClassInput)
    (hU : ∀ i, IsPGroup 2 (U i)) (hh : ∀ i, 0<h i) (n : ℕ)
    (hn : ∀ i, 2*h i≤n) (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-2*h i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (U i) (hn i) (P i)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      fusionPhysicalMenuHot h U (fun i => (C i).prefixDegree)
        (fun i => (C i).liftConstant) (fun i => (C i).gapParameter) n +
      ∑ b ∈ Finset.range n,
        fusionPhysicalMenuRow h U (fun i => (C i).liftConstant)
          (fun i => (C i).gapParameter) n b *
        ((subgroupCount b : ℝ)/exactBenchmark b) :=
  fusionPhysicalUnion_recurrence h U hh n hn F P hP hcover
    (fun i => (C i).prefixDegree) (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) (fun i N J => (C i).momentWeight N J)
    (fun i => (C i).liftConstant_nonneg) (fun i N => ((C i).gapParameter_pos N).le)
    (fun i N J => (C i).momentWeight_nonneg N J)
    (fun i => (C i).original_envelope hMaroti (hU i) (n-2*h i) (P i))
    (fun i N q _hq => (C i).momentWeight_moment_le N (n-2*h i) q)

/-- The actual continuation row contracts from the fixed strict gaps. -/
theorem binaryOrderCharacterSelection_row_contractive (hh : ∀ i, 0<h i) :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n,
        fusionPhysicalMenuRow h U (fun i => (C i).liftConstant)
          (fun i => (C i).gapParameter) n b ≤ 1/2 :=
  fusionPhysicalMenuRow_contractive h U (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) hh (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).gapParameter_pos)

theorem binaryOrderCharacterSelection_row_decay (hh : ∀ i, 0<h i) :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n,
        fusionPhysicalMenuRow h U (fun i => (C i).liftConstant)
          (fun i => (C i).gapParameter) n b ≤ A*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionPhysicalMenuRow_decay h U (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) hh (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).gapParameter_pos)

/-- Global coarse subgroup growth remains an explicit input to hot decay;
it is not supplied by the local action or the character criterion. -/
theorem binaryOrderCharacterSelection_hot_decay
    (hs : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      fusionPhysicalMenuHot h U (fun i => (C i).prefixDegree)
        (fun i => (C i).liftConstant) (fun i => (C i).gapParameter) n ≤
          A*(2:ℝ)^(-κ*(n:ℝ)^2) :=
  fusionPhysicalMenuHot_decay h U hs (fun i => (C i).prefixDegree)
    (fun i => (C i).liftConstant) (fun i => (C i).gapParameter)
    (fun i => (C i).liftConstant_nonneg) (fun i => (C i).gapParameter_pos)

end Menu
end SymmetricSubgroupAsymptotics

end
