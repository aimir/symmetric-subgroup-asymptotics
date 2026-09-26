import SymmetricSubgroupAsymptotics.BinaryTargetOrderMoments
import SymmetricSubgroupAsymptotics.BinaryPhysicalPairFusion

/-! Actual target-order fusion on each literal original normal axis.

For Q = U/N, the central-series Hom bound gives the exact surviving-map
majorant 2^(log2(|Q|)*d2(J)), whose shared-source moment costs 2*log2(|Q|).
A strict gap from the original physical width installs this bound with
D = 1. This does not assert a faithful Q-action of that marker degree.

Each literal normal may select either a physical pair certificate or this
order certificate, before the exterior degree or subgroup is chosen. The
original normalizer divisor, complete exterior and survival predicate stay
in the resulting physical recurrence. Coverage, naturality and exclusions
remain explicit; no conjugacy-class estimate or numerical character-branch
majorant is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

/-- The only additional order-branch obligation is a strict gap between
its binary-marker degree and the literal original permutation degree. -/
structure BinaryTargetOrderCertificate {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal] : Type where
  gap : 2 * Nat.log 2 (Nat.card (U ⧸ N)) < w

namespace BinaryTargetOrderCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]

/-- The actual target order fixes the marker degree. -/
def prefixDegree (_C : BinaryTargetOrderCertificate U N) : ℕ :=
  2 * Nat.log 2 (Nat.card (U ⧸ N))

def liftConstant (_C : BinaryTargetOrderCertificate U N) : ℝ := 1

def gapParameter (C : BinaryTargetOrderCertificate U N) : ℝ :=
  ((w : ℝ) - (C.prefixDegree : ℝ))/16

def momentWeight (_C : BinaryTargetOrderCertificate U N)
    (J : Type*) [Group J] : ℝ := binaryTargetOrderWeight (U ⧸ N) J

variable (C : BinaryTargetOrderCertificate U N)

theorem liftConstant_nonneg : 0 ≤ C.liftConstant := by
  norm_num [liftConstant]

theorem gapParameter_ge_one_sixteenth : (1 : ℝ)/16 ≤ C.gapParameter := by
  have hn : C.prefixDegree + 1 ≤ w := Nat.succ_le_of_lt C.gap
  have hr : (C.prefixDegree : ℝ) + 1 ≤ (w : ℝ) := by exact_mod_cast hn
  unfold gapParameter
  linarith

theorem gapParameter_pos : 0 < C.gapParameter :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/16) C.gapParameter_ge_one_sixteenth

theorem gapParameter_coefficient :
    ((w : ℝ) - (C.prefixDegree : ℝ) - 16*C.gapParameter)/8 = 0 := by
  unfold gapParameter
  ring

theorem momentWeight_nonneg (J : Type*) [Group J] : 0 ≤ C.momentWeight J :=
  binaryTargetOrderWeight_nonneg (U ⧸ N) J

/-- All moments retain one complete original J, and the actual target
quotient is fixed before the sum. This includes moment zero. -/
theorem prefixDegree_moment_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight J^q) ≤
      (subgroupCount (b + q*C.prefixDegree) : ℝ) :=
  binaryTargetOrderWeight_moment_le (U ⧸ N) b q

/-- The exact original surviving onto maps, without an automorphism
quotient or a prior numerical character-envelope assumption. -/
theorem original_survivingEpiCount_le {b : ℕ} (hU : IsPGroup 2 U)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤ C.momentWeight J :=
  binaryTargetOrder_survival_le_weight (hU.to_quotient N)
    (fun f => P (fusionFullGoursatEncode ⟨N, inferInstance⟩ J f).1)

end BinaryTargetOrderCertificate

namespace BinaryTargetOrderCertificate

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))} {N : Subgroup U} [N.Normal]
    (C : BinaryTargetOrderCertificate U N)

/-- The order branch has exactly unit local factor: its entire growth is
in the proved same-source marker weight. -/
theorem fusionLocalFactor_eq (b : ℕ) :
    fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter = 1 := by
  unfold fusionLocalFactor
  rw [C.gapParameter_coefficient]
  simp [liftConstant]

theorem original_survivingEpiCount_le_localFactor {b : ℕ} (hU : IsPGroup 2 U)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  rw [C.fusionLocalFactor_eq b, one_mul]
  exact C.original_survivingEpiCount_le hU P J

end BinaryTargetOrderCertificate

/-- Both alternatives concern the same literal original U and N. -/
abbrev BinaryPairOrderCertificate {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (N : Subgroup U) [N.Normal] :=
  BinaryPhysicalPairCertificate U N ⊕ BinaryTargetOrderCertificate U N

namespace BinaryPairOrderCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (C : BinaryPairOrderCertificate U N)

def prefixDegree : ℕ :=
  match C with
  | .inl B => B.prefixDegree
  | .inr B => B.prefixDegree

def liftConstant : ℝ :=
  match C with
  | .inl B => B.liftConstant
  | .inr B => B.liftConstant

def gapParameter : ℝ :=
  match C with
  | .inl B => B.gapParameter
  | .inr B => B.gapParameter

def momentWeight (J : Type*) [Group J] : ℝ :=
  match C with
  | .inl B => B.momentWeight J
  | .inr B => B.momentWeight J

theorem liftConstant_nonneg : 0 ≤ C.liftConstant := by
  cases C with
  | inl B => exact B.liftConstant_nonneg
  | inr B => exact B.liftConstant_nonneg

theorem gapParameter_pos : 0 < C.gapParameter := by
  cases C with
  | inl B => exact B.gapParameter_pos
  | inr B => exact B.gapParameter_pos

theorem momentWeight_nonneg (J : Type*) [Group J] : 0 ≤ C.momentWeight J := by
  cases C with
  | inl B => exact B.momentWeight_nonneg J
  | inr B => exact B.momentWeight_nonneg J

theorem prefixDegree_moment_le (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight J^q) ≤
      (subgroupCount (b + q*C.prefixDegree) : ℝ) := by
  cases C with
  | inl B => exact B.prefixDegree_moment_le b q
  | inr B => exact B.prefixDegree_moment_le b q

end BinaryPairOrderCertificate

namespace BinaryPairOrderCertificate

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))} {N : Subgroup U} [N.Normal]
    (C : BinaryPairOrderCertificate U N)

theorem original_survivingEpiCount_le_localFactor {b : ℕ} (hU : IsPGroup 2 U)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      fusionLocalFactor b h C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  cases C with
  | inl B => exact B.original_survivingEpiCount_le_localFactor_ambient hU P J
  | inr B => exact B.original_survivingEpiCount_le_localFactor hU P J

end BinaryPairOrderCertificate

/-- Selection is fixed on the complete original normal-axis set; it
cannot depend on exterior J, degree b, or the hot/cold test. -/
abbrev BinaryPairOrderSelection {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w))) :=
  ∀ N : {N : Subgroup U // N.Normal}, Option (BinaryPairOrderCertificate U N.1)

namespace BinaryPairOrderSelection

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} (C : BinaryPairOrderSelection U)

def prefixDegree (N : {N : Subgroup U // N.Normal}) : ℕ :=
  match C N with
  | some B => B.prefixDegree
  | none => 0

def liftConstant (N : {N : Subgroup U // N.Normal}) : ℝ :=
  match C N with
  | some B => B.liftConstant
  | none => 0

def gapParameter (N : {N : Subgroup U // N.Normal}) : ℝ :=
  match C N with
  | some B => B.gapParameter
  | none => 1

def momentWeight (N : {N : Subgroup U // N.Normal}) (J : Type*) [Group J] : ℝ :=
  match C N with
  | some B => B.momentWeight J
  | none => 0

theorem liftConstant_nonneg (N : {N : Subgroup U // N.Normal}) :
    0 ≤ C.liftConstant N := by
  unfold liftConstant
  split
  · exact BinaryPairOrderCertificate.liftConstant_nonneg _
  · exact le_refl 0

theorem gapParameter_pos (N : {N : Subgroup U // N.Normal}) :
    0 < C.gapParameter N := by
  unfold gapParameter
  split
  · exact BinaryPairOrderCertificate.gapParameter_pos _
  · norm_num

theorem momentWeight_nonneg (N : {N : Subgroup U // N.Normal})
    (J : Type*) [Group J] : 0 ≤ C.momentWeight N J := by
  unfold momentWeight
  split
  · exact BinaryPairOrderCertificate.momentWeight_nonneg _ _
  · exact le_refl 0

theorem momentWeight_moment_le (N : {N : Subgroup U // N.Normal}) (b q : ℕ)
    (hq : 1 ≤ q) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight N J ^ q) ≤
      (subgroupCount (b + q * C.prefixDegree N) : ℝ) := by
  cases hc : C N with
  | none => simp [momentWeight, prefixDegree, hc, Nat.ne_of_gt (by omega : 0 < q)]
  | some B =>
    simpa only [momentWeight, prefixDegree, hc] using B.prefixDegree_moment_le b q

end BinaryPairOrderSelection

namespace BinaryPairOrderSelection

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    (C : BinaryPairOrderSelection U)

/-- The selected bound is proved on every surviving original map. There
is no axiswise naturality requirement on the certificate choice. -/
theorem original_envelope (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hexcluded : ∀ N, C N = none → ∀ J, fusionSurvivingEpiCount U P N J = 0)
    (N : {N : Subgroup U // N.Normal}) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b h (C.prefixDegree N) (C.liftConstant N) (C.gapParameter N) *
        C.momentWeight N J := by
  cases hc : C N with
  | none => simp [hexcluded N hc J, momentWeight, hc]
  | some B =>
    simpa only [prefixDegree, liftConstant, gapParameter, momentWeight, hc] using
      B.original_survivingEpiCount_le_localFactor hU P J

/-- Original physical pointing keeps its actual normalizer divisor for
both branches. No marker or quotient normalizer replaces that divisor. -/
theorem physical_kernel_bound (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P)
    (hexcluded : ∀ N, C N = none → ∀ J, fusionSurvivingEpiCount U P N J = 0) :
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
    (C.original_envelope hU b P hexcluded) (fun N q hq => C.momentWeight_moment_le N b q hq)

end BinaryPairOrderSelection

section Menu

variable {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))
    (C : ∀ i, BinaryPairOrderSelection (U i))

/-- A literal finite cover gives the original-weight recurrence using
proved pair/order envelopes and moments. No class-count input occurs. -/
theorem binaryPairOrderSelection_recurrence
    (hU : ∀ i, IsPGroup 2 (U i)) (hh : ∀ i, 0<h i) (n : ℕ)
    (hn : ∀ i, 2*h i≤n) (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-2*h i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (U i) (hn i) (P i))
    (hexcluded : ∀ i N, C i N = none → ∀ J,
      fusionSurvivingEpiCount (U i) (P i) N J = 0) :
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
    (fun i => (C i).original_envelope (hU i) (n-2*h i) (P i) (hexcluded i))
    (fun i N q hq => (C i).momentWeight_moment_le N (n-2*h i) q hq)

/-- The actual continuation row contracts from the strict local gaps,
without assuming a bound on the normalized total subgroup count. -/
theorem binaryPairOrderSelection_row_contractive (hh : ∀ i, 0<h i) :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n,
        fusionPhysicalMenuRow h U (fun i => (C i).liftConstant)
          (fun i => (C i).gapParameter) n b ≤ 1/2 :=
  fusionPhysicalMenuRow_contractive h U (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) hh (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).gapParameter_pos)

theorem binaryPairOrderSelection_row_decay (hh : ∀ i, 0<h i) :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n,
        fusionPhysicalMenuRow h U (fun i => (C i).liftConstant)
          (fun i => (C i).gapParameter) n b ≤ A*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionPhysicalMenuRow_decay h U (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) hh (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).gapParameter_pos)

/-- Hot decay keeps the same explicit global coarse estimate as the
existing physical fusion theorem. It is not inferred from a local axis. -/
theorem binaryPairOrderSelection_hot_decay
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
