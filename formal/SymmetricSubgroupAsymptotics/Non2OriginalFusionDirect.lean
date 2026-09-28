import SymmetricSubgroupAsymptotics.Non2OriginalFusion
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterDirectFusion

/-!
# Direct continuation for a finite menu of nonbinary fusion certificates

The retained nonbinary cut already supplies all data needed by the exact
first-moment physical union.  This file installs a finite family of distinct
original actions and literal normal axes into one shifted recurrence row.
The same row is forward, exponentially decaying and eventually contractive.
All quotient groups, module sections, extension charts and faithful top
covers remain axis-dependent.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

section Menu

variable {ι : Type*} [Fintype ι]
variable (s : ι → ℕ)
variable (U : ∀ i, Subgroup (Equiv.Perm (Fin (2 * s i))))
variable (B₀ : ∀ i, {N : Subgroup (U i) // N.Normal} → Type)
variable [∀ i N, Group (B₀ i N)] [∀ i N, Finite (B₀ i N)]
variable (M₀ : ∀ i N, Rep (ZMod 2) (B₀ i N))
variable [∀ i N, Finite (M₀ i N)]
variable (C₀ : ∀ i N, Non2OriginalFusionCertificate (M₀ i N) (s i))

/-- The exact original-action row produced by the retained nonbinary cuts.
Every literal normal axis keeps its own shifted degree, lift constant and
capacity gap. -/
def non2OriginalFusionDirectRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow s U
    (fun i N => (C₀ i N).prefixDegree)
    (fun i N => (C₀ i N).liftConstant)
    (fun i N => (C₀ i N).gapParameter) n m

omit [∀ i N, Finite (B₀ i N)] [∀ i N, Finite (M₀ i N)] in
theorem non2OriginalFusionDirectRow_nonneg (n m : ℕ) :
    0 ≤ non2OriginalFusionDirectRow s U B₀ M₀ C₀ n m :=
  fusionPhysicalDirectRow_nonneg s U _ _ _
    (fun i N => (C₀ i N).liftConstant_nonneg) n m

omit [∀ i N, Finite (B₀ i N)] in
theorem non2OriginalFusionDirectRow_forward
    (hs : ∀ i, 24 ≤ s i) {n m : ℕ} (hnm : n ≤ m) :
    non2OriginalFusionDirectRow s U B₀ M₀ C₀ n m = 0 :=
  fusionPhysicalDirectRow_forward s U _ _ _
    (fun i N => (C₀ i N).prefixDegree_lt (hs i)) hnm

/-- Complete physical coverage by the chosen finite action menu gives one
forward recurrence.  The source predicate is evaluated on the unchanged
complete complement, and every normal axis keeps its actual quotient and
nonsplit extension. -/
theorem non2OriginalFusion_direct_recurrence
    (hs : ∀ i, 24 ≤ s i)
    (n : ℕ) (hn : ∀ i, 2 * s i ≤ n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i,
      Subgroup (U i × Equiv.Perm (Fin (n - 2 * s i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H ∈ F, ∃ i,
      H ∈ FusionCanonicalFamily (U i) (hn i) (P i))
    (π : ∀ i N, (U i ⧸ N.1) →* B₀ i N)
    (hπ : ∀ i N, Function.Surjective (π i N))
    (E : ∀ i N, OriginalKernelModuleChart (π i N) (M₀ i N))
    (T : ∀ i, {N : Subgroup (U i) // N.Normal} → Type)
    [∀ i N, Group (T i N)]
    (ρ : ∀ i N, T i N →* Equiv.Perm (Fin (s i)))
    (hρ : ∀ i N, Function.Injective (ρ i N))
    (σ : ∀ i N, T i N →* B₀ i N)
    (hσ : ∀ i N, Function.Surjective (σ i N)) :
    (Nat.card F : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n,
        non2OriginalFusionDirectRow s U B₀ M₀ C₀ n m *
          ((subgroupCount m : ℝ) / exactBenchmark m) := by
  apply fusionPhysicalUnion_direct_recurrence s U n hn F P hP hcover
    (fun i N => (C₀ i N).prefixDegree)
    (fun i N => (C₀ i N).liftConstant)
    (fun i N => (C₀ i N).gapParameter)
    (fun i N J => (C₀ i N).momentWeight J)
  · intro i N
    exact (C₀ i N).prefixDegree_lt (hs i)
  · intro i N
    exact (C₀ i N).liftConstant_nonneg
  · intro i N J
    exact (C₀ i N).fusionSurvivingEpiCount_le
      (U i) N (π i N) (hπ i N) (E i N) (P i) J
  · intro i N
    simpa only [pow_one, one_mul] using
      (C₀ i N).momentWeight_moment_le
        (ρ i N) (hρ i N) (σ i N) (hσ i N) (n - 2 * s i) 1

omit [∀ i N, Finite (B₀ i N)] in
/-- The complete finite original-weight row decays exponentially.  This is
a numerical consequence of the checked prefix and gap; it assumes no bound
on the unknown subgroup-count sequence. -/
theorem non2OriginalFusionDirectRow_decay
    (hs : ∀ i, 24 ≤ s i) (heven : ∀ i, Even (s i)) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n,
        non2OriginalFusionDirectRow s U B₀ M₀ C₀ n m ≤
          A * (2 : ℝ) ^ (-κ * (n : ℝ)) :=
  fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis s U => s j.1)
    (fun j => (C₀ j.1 j.2).prefixDegree)
    (fun j => (C₀ j.1 j.2).markerHalf)
    (fun j => (C₀ j.1 j.2).liftConstant)
    (fun j => fusionPhysicalMenuDivisor s U j.1)
    (fun j => (C₀ j.1 j.2).gapParameter)
    (fun j => (C₀ j.1 j.2).prefixDegree_lt (hs j.1))
    (fun j => (C₀ j.1 j.2).prefixDegree_eq_two_mul_markerHalf
      (heven j.1))
    (fun j => (C₀ j.1 j.2).liftConstant_nonneg)
    (fun j => fusionPhysicalMenuDivisor_pos s U j.1)
    (fun j => (C₀ j.1 j.2).gapParameter_pos (hs j.1))

omit [∀ i N, Finite (B₀ i N)] in
/-- Eventual contraction of the same literal row. -/
theorem non2OriginalFusionDirectRow_contractive
    (hs : ∀ i, 24 ≤ s i) (heven : ∀ i, Even (s i)) :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n,
        non2OriginalFusionDirectRow s U B₀ M₀ C₀ n m ≤ 1 / 2 :=
  fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis s U => s j.1)
    (fun j => (C₀ j.1 j.2).prefixDegree)
    (fun j => (C₀ j.1 j.2).markerHalf)
    (fun j => (C₀ j.1 j.2).liftConstant)
    (fun j => fusionPhysicalMenuDivisor s U j.1)
    (fun j => (C₀ j.1 j.2).gapParameter)
    (fun j => (C₀ j.1 j.2).prefixDegree_lt (hs j.1))
    (fun j => (C₀ j.1 j.2).prefixDegree_eq_two_mul_markerHalf
      (heven j.1))
    (fun j => (C₀ j.1 j.2).liftConstant_nonneg)
    (fun j => fusionPhysicalMenuDivisor_pos s U j.1)
    (fun j => (C₀ j.1 j.2).gapParameter_pos (hs j.1))

end Menu

end SymmetricSubgroupAsymptotics

end
