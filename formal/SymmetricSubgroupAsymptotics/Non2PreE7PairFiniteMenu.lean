import SymmetricSubgroupAsymptotics.Non2PreE7PairPayload
import SymmetricSubgroupAsymptotics.Non2OriginalFusionPayloadSelection
import SymmetricSubgroupAsymptotics.ForwardEstimateAlgebra

/-!
# Finite residual pair menus on the pre-E7 frontier

The universal arbitrary-axis payload is assembled here over any finite family
of pair widths.  The counted index contains only original action conjugacy
classes; pair frames and normal-axis payloads are chosen after that index is
fixed.  The resulting physical union has an exact original-weight recurrence
and an exponentially decaying forward estimate.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

section Menu

variable {κ : Type*} [Fintype κ]
variable (s : κ → ℕ)

/-- Original pre-`E7` pair actions over a finite family of half-widths. -/
abbrev PreE7PairMenuIndex :=
  Σ k : κ, PreE7PairActionClass (s k)

instance preE7PairMenuIndexFintype : Fintype (PreE7PairMenuIndex s) :=
  Fintype.ofFinite _

def preE7PairMenuHalfWidth (i : PreE7PairMenuIndex s) : ℕ :=
  s i.1

def preE7PairMenuAction (i : PreE7PairMenuIndex s) :
    Subgroup (Equiv.Perm (Fin (2 * preE7PairMenuHalfWidth s i))) :=
  preE7PairAction (s i.1) i.2

/-- Complete arbitrary-normal-axis payload on the finite residual pair menu. -/
noncomputable def preE7PairMenuAxisPayload
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : ∀ k, 24 ≤ s k) (heven : ∀ k, Even (s k))
    (i : PreE7PairMenuIndex s)
    (N : {N : Subgroup (preE7PairMenuAction s i) // N.Normal}) :
    Non2OriginalFusionAxisPayload (preE7PairMenuHalfWidth s i)
      (preE7PairMenuAction s i) N :=
  preE7PairAxisPayload hTracey hExceptional (hs i.1) (heven i.1) i.2 N

/-- Exact original-weight row for the complete finite residual pair menu. -/
def preE7PairMenuDirectRow
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : ∀ k, 24 ≤ s k) (heven : ∀ k, Even (s k))
    (n m : ℕ) : ℝ :=
  non2OriginalFusionPayloadDirectRow
    (preE7PairMenuHalfWidth s) (preE7PairMenuAction s)
    (fun i N => some
      (preE7PairMenuAxisPayload s hTracey hExceptional hs heven i N)) n m

theorem preE7PairMenuDirectRow_nonneg
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : ∀ k, 24 ≤ s k) (heven : ∀ k, Even (s k))
    (n m : ℕ) :
    0 ≤ preE7PairMenuDirectRow s hTracey hExceptional hs heven n m :=
  non2OriginalFusionPayloadDirectRow_nonneg
    (preE7PairMenuHalfWidth s) (preE7PairMenuAction s)
    (fun i N => some
      (preE7PairMenuAxisPayload s hTracey hExceptional hs heven i N)) n m

theorem preE7PairMenuDirectRow_forward
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : ∀ k, 24 ≤ s k) (heven : ∀ k, Even (s k))
    {n m : ℕ} (hnm : n ≤ m) :
    preE7PairMenuDirectRow s hTracey hExceptional hs heven n m = 0 :=
  non2OriginalFusionPayloadDirectRow_forward
    (preE7PairMenuHalfWidth s) (preE7PairMenuAction s)
    (fun i N => some
      (preE7PairMenuAxisPayload s hTracey hExceptional hs heven i N))
    (fun i => hs i.1) hnm

/-- The literal physical union covered by the finite residual pair menu. -/
def PreE7PairMenuPhysical (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ (i : PreE7PairMenuIndex s)
      (hi : 2 * preE7PairMenuHalfWidth s i ≤ n),
    H ∈ FusionCanonicalFamily (preE7PairMenuAction s i) hi
      (preE7Predicate (2 * preE7PairMenuHalfWidth s i) i.2.1
        (n - 2 * preE7PairMenuHalfWidth s i))}

/-- Exact recurrence for the complete physical union.  All normal axes are
selected, so the zero-fibre side condition is discharged definitionally. -/
theorem preE7PairMenuPhysical_direct_recurrence
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : ∀ k, 24 ≤ s k) (heven : ∀ k, Even (s k))
    (n : ℕ)
    (hn : ∀ i : PreE7PairMenuIndex s,
      2 * preE7PairMenuHalfWidth s i ≤ n) :
    (Nat.card (PreE7PairMenuPhysical s n) : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n,
        preE7PairMenuDirectRow s hTracey hExceptional hs heven n m *
          ordinarySubgroupRatio m := by
  apply non2OriginalFusion_payload_direct_recurrence
    (preE7PairMenuHalfWidth s) (preE7PairMenuAction s)
    (fun i N => some
      (preE7PairMenuAxisPayload s hTracey hExceptional hs heven i N))
    (fun i => hs i.1) n hn (PreE7PairMenuPhysical s n)
    (fun i => preE7Predicate (2 * preE7PairMenuHalfWidth s i) i.2.1
      (n - 2 * preE7PairMenuHalfWidth s i))
  · intro i
    exact preE7Predicate_natural
      (2 * preE7PairMenuHalfWidth s i) i.2.1
      (n - 2 * preE7PairMenuHalfWidth s i)
  · intro H hH
    rcases hH with ⟨i, hi, hH⟩
    refine ⟨i, ?_⟩
    simpa only using hH
  · intro i N hnone J
    simp at hnone

/-- Uniform exponential row deficit for every finite residual pair menu. -/
theorem preE7PairMenuDirectRow_decay
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : ∀ k, 24 ≤ s k) (heven : ∀ k, Even (s k)) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n,
        preE7PairMenuDirectRow s hTracey hExceptional hs heven n m ≤
          A * (2 : ℝ) ^ (-κ * (n : ℝ)) :=
  non2OriginalFusionPayloadDirectRow_decay
    (preE7PairMenuHalfWidth s) (preE7PairMenuAction s)
    (fun i N => some
      (preE7PairMenuAxisPayload s hTracey hExceptional hs heven i N))
    (fun i => hs i.1) (fun i => heven i.1)

/-- Ambient-degree normalized count of the finite residual pair union. -/
def preE7PairMenuPhysicalRatio (n : ℕ) : ℝ :=
  (Nat.card (PreE7PairMenuPhysical s n) : ℝ) / exactBenchmark n

/-- Every finite residual pair menu is a complete exponentially contractive
forward sector. -/
noncomputable def preE7PairMenuPhysical_exponentialForwardEstimate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hs : ∀ k, 24 ≤ s k) (heven : ∀ k, Even (s k))
    (widthBound : ℕ) (hwidth : ∀ k, 2 * s k ≤ widthBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      (preE7PairMenuPhysicalRatio s) := by
  let W := preE7PairMenuDirectRow_decay s hTracey hExceptional hs heven
  let A : ℝ := Classical.choose W
  have hAκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hAκ
  have hdecaySpec := Classical.choose_spec hAκ
  have hA : 0 < A := hdecaySpec.1
  have hκ : 0 < κ := hdecaySpec.2.1
  have hdecay := hdecaySpec.2.2
  let V := eventually_atTop.mp hdecay
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := preE7PairMenuDirectRow s hTracey hExceptional hs heven
      threshold := max widthBound N
      rate := κ
      scalarConst := 1
      rowConst := A
      rate_pos := hκ
      scalarConst_pos := by norm_num
      rowConst_nonneg := hA.le
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ m _
    exact preE7PairMenuDirectRow_nonneg
      s hTracey hExceptional hs heven n m
  · intro n hn
    have hnwidth : widthBound ≤ n := (le_max_left widthBound N).trans hn
    exact (preE7PairMenuPhysical_direct_recurrence
      s hTracey hExceptional hs heven n
      (fun i => (hwidth i.1).trans hnwidth)).trans_eq (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right widthBound N).trans hn)

end Menu

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
