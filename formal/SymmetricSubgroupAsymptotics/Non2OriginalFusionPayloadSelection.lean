import SymmetricSubgroupAsymptotics.Non2OriginalFusionDirect

/-!
# Optional complete payloads for residual nonbinary fusion

An earlier-owned normal axis need not carry dummy quotient, module, extension,
or faithful-cover data.  This file therefore makes the whole nonbinary fusion
payload optional.  A selected axis carries every object used by the local
envelope and same-source moment; an absent axis is allowed only when its
residual surviving-epimorphism fibre is empty on every complete source.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- All data used by the nonbinary local envelope and first moment on one
literal original normal axis. -/
structure Non2OriginalFusionAxisPayload (s : ℕ)
    (U : Subgroup (Equiv.Perm (Fin (2 * s))))
    (N : {N : Subgroup U // N.Normal}) where
  B : Type
  [groupB : Group B]
  [finiteB : Finite B]
  M : Rep (ZMod 2) B
  [finiteM : Finite M]
  certificate : Non2OriginalFusionCertificate M s
  base : (U ⧸ N.1) →* B
  base_surjective : Function.Surjective base
  moduleChart : OriginalKernelModuleChart base M
  T : Type
  [groupT : Group T]
  topAction : T →* Equiv.Perm (Fin s)
  topAction_injective : Function.Injective topAction
  topBase : T →* B
  topBase_surjective : Function.Surjective topBase

attribute [instance]
  Non2OriginalFusionAxisPayload.groupB
  Non2OriginalFusionAxisPayload.finiteB
  Non2OriginalFusionAxisPayload.finiteM
  Non2OriginalFusionAxisPayload.groupT

section Menu

variable {ι : Type*} [Fintype ι]
variable (s : ι → ℕ)
variable (U : ∀ i, Subgroup (Equiv.Perm (Fin (2 * s i))))
variable (C₀ : ∀ i (N : {N : Subgroup (U i) // N.Normal}),
  Option (Non2OriginalFusionAxisPayload (s i) (U i) N))

def non2PayloadPrefixDegree (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) : ℕ :=
  match C₀ i N with
  | some A => A.certificate.prefixDegree
  | none => 0

def non2PayloadMarkerHalf (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) : ℕ :=
  match C₀ i N with
  | some A => A.certificate.markerHalf
  | none => 0

def non2PayloadLiftConstant (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) : ℝ :=
  match C₀ i N with
  | some A => A.certificate.liftConstant
  | none => 0

def non2PayloadGapParameter (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) : ℝ :=
  match C₀ i N with
  | some A => A.certificate.gapParameter
  | none => 1

def non2PayloadMomentWeight (i : ι)
    (N : {N : Subgroup (U i) // N.Normal})
    (J : Type*) [Group J] : ℝ :=
  match C₀ i N with
  | some A => A.certificate.momentWeight J
  | none => 0

omit [Fintype ι] in
theorem non2PayloadPrefixDegree_lt
    (hs : ∀ i, 24 ≤ s i) (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) :
    non2PayloadPrefixDegree s U C₀ i N < 2 * s i := by
  cases hc : C₀ i N with
  | none =>
      have hpos : 0 < s i := by have := hs i; omega
      simp [non2PayloadPrefixDegree, hc]
      omega
  | some A =>
      simpa [non2PayloadPrefixDegree, hc] using
        A.certificate.prefixDegree_lt (hs i)

omit [Fintype ι] in
theorem non2PayloadPrefixDegree_eq_two_mul
    (heven : ∀ i, Even (s i)) (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) :
    non2PayloadPrefixDegree s U C₀ i N =
      2 * non2PayloadMarkerHalf s U C₀ i N := by
  cases hc : C₀ i N with
  | none => simp [non2PayloadPrefixDegree, non2PayloadMarkerHalf, hc]
  | some A =>
      simpa [non2PayloadPrefixDegree, non2PayloadMarkerHalf, hc] using
        A.certificate.prefixDegree_eq_two_mul_markerHalf (heven i)

omit [Fintype ι] in
theorem non2PayloadLiftConstant_nonneg (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) :
    0 ≤ non2PayloadLiftConstant s U C₀ i N := by
  cases hc : C₀ i N with
  | none => simp [non2PayloadLiftConstant, hc]
  | some A =>
      simpa [non2PayloadLiftConstant, hc] using
        A.certificate.liftConstant_nonneg

omit [Fintype ι] in
theorem non2PayloadGapParameter_pos
    (hs : ∀ i, 24 ≤ s i) (i : ι)
    (N : {N : Subgroup (U i) // N.Normal}) :
    0 < non2PayloadGapParameter s U C₀ i N := by
  cases hc : C₀ i N with
  | none => simp [non2PayloadGapParameter, hc]
  | some A =>
      simpa [non2PayloadGapParameter, hc] using
        A.certificate.gapParameter_pos (hs i)

/-- Direct row of the complete-payload selection.  Every absent axis remains
in the original normal sum with coefficient zero. -/
def non2OriginalFusionPayloadDirectRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow s U
    (non2PayloadPrefixDegree s U C₀)
    (non2PayloadLiftConstant s U C₀)
    (non2PayloadGapParameter s U C₀) n m

theorem non2OriginalFusionPayloadDirectRow_nonneg (n m : ℕ) :
    0 ≤ non2OriginalFusionPayloadDirectRow s U C₀ n m :=
  fusionPhysicalDirectRow_nonneg s U _ _ _
    (non2PayloadLiftConstant_nonneg s U C₀) n m

theorem non2OriginalFusionPayloadDirectRow_forward
    (hs : ∀ i, 24 ≤ s i) {n m : ℕ} (hnm : n ≤ m) :
    non2OriginalFusionPayloadDirectRow s U C₀ n m = 0 :=
  fusionPhysicalDirectRow_forward s U _ _ _
    (non2PayloadPrefixDegree_lt s U C₀ hs) hnm

/-- Exact residual recurrence with no dummy data on earlier-owned axes. -/
theorem non2OriginalFusion_payload_direct_recurrence
    (hs : ∀ i, 24 ≤ s i)
    (n : ℕ) (hn : ∀ i, 2 * s i ≤ n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i,
      Subgroup (U i × Equiv.Perm (Fin (n - 2 * s i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H ∈ F, ∃ i,
      H ∈ FusionCanonicalFamily (U i) (hn i) (P i))
    (hexcluded : ∀ i N, C₀ i N = none → ∀ J,
      fusionSurvivingEpiCount (U i) (P i) N J = 0) :
    (Nat.card F : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n,
        non2OriginalFusionPayloadDirectRow s U C₀ n m *
          ((subgroupCount m : ℝ) / exactBenchmark m) := by
  apply fusionPhysicalUnion_direct_recurrence s U n hn F P hP hcover
    (non2PayloadPrefixDegree s U C₀)
    (non2PayloadLiftConstant s U C₀)
    (non2PayloadGapParameter s U C₀)
    (fun i N J => non2PayloadMomentWeight s U C₀ i N J)
  · exact non2PayloadPrefixDegree_lt s U C₀ hs
  · exact non2PayloadLiftConstant_nonneg s U C₀
  · intro i N J
    cases hc : C₀ i N with
    | none =>
        simp [hexcluded i N hc J, non2PayloadLiftConstant,
          non2PayloadMomentWeight, hc]
    | some A =>
        simpa [non2PayloadPrefixDegree, non2PayloadLiftConstant,
          non2PayloadGapParameter, non2PayloadMomentWeight, hc] using
          A.certificate.fusionSurvivingEpiCount_le
            (U i) N A.base A.base_surjective A.moduleChart (P i) J
  · intro i N
    cases hc : C₀ i N with
    | none =>
        simp [non2PayloadMomentWeight, non2PayloadPrefixDegree, hc]
    | some A =>
        simpa [non2PayloadMomentWeight, non2PayloadPrefixDegree, hc,
          pow_one, one_mul] using
          A.certificate.momentWeight_moment_le
            A.topAction A.topAction_injective A.topBase A.topBase_surjective
            (n - 2 * s i) 1

theorem non2OriginalFusionPayloadDirectRow_decay
    (hs : ∀ i, 24 ≤ s i) (heven : ∀ i, Even (s i)) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n,
        non2OriginalFusionPayloadDirectRow s U C₀ n m ≤
          A * (2 : ℝ) ^ (-κ * (n : ℝ)) :=
  fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis s U => s j.1)
    (fun j => non2PayloadPrefixDegree s U C₀ j.1 j.2)
    (fun j => non2PayloadMarkerHalf s U C₀ j.1 j.2)
    (fun j => non2PayloadLiftConstant s U C₀ j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor s U j.1)
    (fun j => non2PayloadGapParameter s U C₀ j.1 j.2)
    (fun j => non2PayloadPrefixDegree_lt s U C₀ hs j.1 j.2)
    (fun j => non2PayloadPrefixDegree_eq_two_mul
      s U C₀ heven j.1 j.2)
    (fun j => non2PayloadLiftConstant_nonneg s U C₀ j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos s U j.1)
    (fun j => non2PayloadGapParameter_pos s U C₀ hs j.1 j.2)

theorem non2OriginalFusionPayloadDirectRow_contractive
    (hs : ∀ i, 24 ≤ s i) (heven : ∀ i, Even (s i)) :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n,
        non2OriginalFusionPayloadDirectRow s U C₀ n m ≤ 1 / 2 :=
  fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis s U => s j.1)
    (fun j => non2PayloadPrefixDegree s U C₀ j.1 j.2)
    (fun j => non2PayloadMarkerHalf s U C₀ j.1 j.2)
    (fun j => non2PayloadLiftConstant s U C₀ j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor s U j.1)
    (fun j => non2PayloadGapParameter s U C₀ j.1 j.2)
    (fun j => non2PayloadPrefixDegree_lt s U C₀ hs j.1 j.2)
    (fun j => non2PayloadPrefixDegree_eq_two_mul
      s U C₀ heven j.1 j.2)
    (fun j => non2PayloadLiftConstant_nonneg s U C₀ j.1 j.2)
    (fun j => fusionPhysicalMenuDivisor_pos s U j.1)
    (fun j => non2PayloadGapParameter_pos s U C₀ hs j.1 j.2)

end Menu

end SymmetricSubgroupAsymptotics

end
