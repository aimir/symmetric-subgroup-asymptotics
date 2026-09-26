import SymmetricSubgroupAsymptotics.BinaryPhysicalPairParameters
import SymmetricSubgroupAsymptotics.FusionPhysicalUnion

/-! Original-weight fusion for selected physical pair certificates.

A certificate is chosen once for each literal normal, independently of the
exterior subgroup and degree. An absent certificate means that this physical
family has no surviving epimorphism on that axis. All counting envelopes,
shared-source moments, numerical gaps and continuation row bounds are derived.
The action cover and the exclusion of absent axes remain structural inputs.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

/-- Selection is on the complete original normal-axis set, before choosing J. -/
abbrev BinaryPairSelection {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w))) :=
  ∀ N : {N : Subgroup U // N.Normal}, Option (BinaryPhysicalPairCertificate U N.1)

namespace BinaryPairSelection

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} (C : BinaryPairSelection U)

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
  · exact BinaryPhysicalPairCertificate.liftConstant_nonneg _
  · exact le_refl 0

theorem gapParameter_pos (N : {N : Subgroup U // N.Normal}) :
    0 < C.gapParameter N := by
  unfold gapParameter
  split
  · exact BinaryPhysicalPairCertificate.gapParameter_pos _
  · norm_num

theorem momentWeight_nonneg (N : {N : Subgroup U // N.Normal})
    (J : Type*) [Group J] : 0 ≤ C.momentWeight N J := by
  unfold momentWeight
  split
  · exact BinaryPhysicalPairCertificate.momentWeight_nonneg _ _
  · exact le_refl 0

theorem momentWeight_moment_le (N : {N : Subgroup U // N.Normal}) (b q : ℕ)
    (hq : 1 ≤ q) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight N J ^ q) ≤
      (subgroupCount (b + q * C.prefixDegree N) : ℝ) := by
  cases hc : C N with
  | none => simp [momentWeight, prefixDegree, hc, Nat.ne_of_gt (by omega : 0 < q)]
  | some B =>
    simpa only [momentWeight, prefixDegree, hc] using B.prefixDegree_moment_le b q

end BinaryPairSelection

namespace BinaryPairSelection

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    (C : BinaryPairSelection U)

/-- No condition is imposed on a chosen certificate's behavior under the
normalizer: naturality is required only of the complete physical family. -/
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
      B.original_survivingEpiCount_le_localFactor_ambient hU P J

/-- Both numerical kernels now follow from the selected original pair
certificates. The original action normalizer divides the entire axis sum. -/
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

end BinaryPairSelection

section Menu

variable {ι : Type*} [Fintype ι] (h : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))
    (C : ∀ i, BinaryPairSelection (U i))

/-- A literal cover by the selected pair families gives the full original
weighted recurrence for that cover, with no supplied envelope or moment. -/
theorem binaryPairSelection_recurrence
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

/-- The same row appearing in the actual recurrence contracts. Certificate
choices and their constants are fixed before varying the ambient degree. -/
theorem binaryPairSelection_row_contractive (hh : ∀ i, 0<h i) :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n,
        fusionPhysicalMenuRow h U (fun i => (C i).liftConstant)
          (fun i => (C i).gapParameter) n b ≤ 1/2 :=
  fusionPhysicalMenuRow_contractive h U (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) hh (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).gapParameter_pos)

theorem binaryPairSelection_row_decay (hh : ∀ i, 0<h i) :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n,
        fusionPhysicalMenuRow h U (fun i => (C i).liftConstant)
          (fun i => (C i).gapParameter) n b ≤ A*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionPhysicalMenuRow_decay h U (fun i => (C i).liftConstant)
    (fun i => (C i).gapParameter) hh (fun i => (C i).liftConstant_nonneg)
    (fun i => (C i).gapParameter_pos)

/-- Hot decay retains the explicit coarse subgroup estimate required by the
generic hot-kernel theorem; that global input is not proved by a local pair. -/
theorem binaryPairSelection_hot_decay
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
