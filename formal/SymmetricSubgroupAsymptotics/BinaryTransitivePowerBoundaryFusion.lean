import SymmetricSubgroupAsymptotics.BinaryOrderPrunedNontrivialAxes
import SymmetricSubgroupAsymptotics.BinaryTransitivePowerCharacterCriterion
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterFusion

/-!
# Complete boundary selections at power-of-two degrees

An original transitive action of degree `2^k`, with `k ≥ 4` and order at
most `2^(2^(k-1))`, receives a certificate on every original normal axis.
Nontrivial normals save one order bit. When the source is not already
small enough, the bottom axis uses the original faithful action's character
criterion. All choices precede the exterior group and survival predicate.

The physical and finite-menu statements retain the binary-source and
class-count hypotheses, original normalizers, and actual physical cover.
The menu is fixed and finite; no bound over all varying degrees is asserted.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryTransitivePowerBoundaryFusion

/-- Exact original width as twice its half-width. -/
theorem two_mul_half (k : ℕ) (hk : 1 ≤ k) :
    2 * 2^(k-1) = 2^k := by
  calc
    2 * 2^(k-1) = 2^((k-1)+1) := by rw [pow_succ, Nat.mul_comm]
    _ = 2^k := by rw [Nat.sub_add_cancel hk]

/-- The small-source order threshold contains the regular action's order.
The proof is symbolic after its degree-sixteen initial case. -/
theorem degree_exponent_lt_half (k : ℕ) (hk : 4 ≤ k) :
    k < 2^(k-1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      rw [Nat.succ_sub_one, ← two_mul_half k (by omega)]
      omega

theorem degree_le_order_threshold (k : ℕ) (hk : 4 ≤ k) :
    2^k ≤ 2^(2^(k-1)-1) :=
  Nat.pow_le_pow_right (by decide : 0 < 2)
    (by have h := degree_exponent_lt_half k hk; omega)

theorem order_marker_gap (k : ℕ) (hk : 1 ≤ k) :
    2 * (2^(k-1)-1) < 2^k := by
  have hhalf : 0 < 2^(k-1) := pow_pos (by decide : 0 < 2) _
  have hwidth := two_mul_half k hk
  omega

section Selection

variable {w : ℕ} (k : ℕ) (hk : 4 ≤ k)
    (U : Subgroup (Equiv.Perm (Fin w)))
    [MulAction.IsPretransitive U (Fin w)]
    (hdegree : w = 2^k)

/-- Change only the numerical width of the criterion. The original group,
its original points, and its literal bottom quotient are never relabelled. -/
def botCharacterCriterionOfDegree (hlarge : 2^k < Nat.card U) :
    BinaryNormalCharacterCriterion (U ⧸ (⊥ : Subgroup U)) w := by
  have hw : 0 < w := by rw [hdegree]; exact pow_pos (by decide : 0 < 2) k
  letI : Nonempty (Fin w) := ⟨⟨0, hw⟩⟩
  let C := (binaryTransitivePower_characterCriterion (G := U) (X := Fin w)
    k hk (by simpa only [Nat.card_fin] using hdegree) hlarge).transport
      (QuotientGroup.quotientBot (G := U)).symm
  exact {
    dimension := C.dimension
    cardinal := C.cardinal
    gap := by simpa only [hdegree] using C.gap }

/-- A complete choice on all literal original normals. The actual binary
hypothesis is needed by the counting consumer, not by this order selection. -/
def selectionOfDegree (hcard : Nat.card U ≤ 2^(2^(k-1))) :
    BinaryOrderCharacterSelection U := by
  rintro ⟨N, hNormal⟩
  letI := hNormal
  have hgap : 2 * (2^(k-1)-1) < w := by
    rw [hdegree]
    exact order_marker_gap k (by omega)
  by_cases hsmall : Nat.card U ≤ 2^(2^(k-1)-1)
  · exact .inl (BinaryOrderPrunedCoverage.certificateOfCard U N hsmall hgap)
  · by_cases hN : N = ⊥
    · subst N
      have hlarge : 2^k < Nat.card U :=
        (degree_le_order_threshold k hk).trans_lt (Nat.lt_of_not_ge hsmall)
      exact .inr (botCharacterCriterionOfDegree k hk U hdegree hlarge)
    · have hhalf : 1 ≤ 2^(k-1) := Nat.one_le_pow _ _ (by decide)
      have hcard' : Nat.card U ≤ 2^((2^(k-1)-1)+1) := by
        simpa only [Nat.sub_add_cancel hhalf] using hcard
      exact .inl (BinaryOrderPrunedNontrivialAxes.certificateOfNontrivial
        U N hcard' hN hgap)

/-- The selected marker always leaves at least two original points. -/
theorem selectionOfDegree_prefixDegree_le
    (hcard : Nat.card U ≤ 2^(2^(k-1))) (N : {N : Subgroup U // N.Normal}) :
    (selectionOfDegree k hk U hdegree hcard).prefixDegree N ≤
      2 * (2^(k-1)-1) := by
  change ((selectionOfDegree k hk U hdegree hcard) N).prefixDegree ≤ _
  cases hC : (selectionOfDegree k hk U hdegree hcard) N with
  | inl C =>
      change 2 * Nat.log 2 (Nat.card (U ⧸ N.1)) ≤ _
      have h := C.gap
      have hwidth := two_mul_half k (by omega)
      omega
  | inr C => exact Nat.zero_le _

end Selection

/-- Direct literal power-width entry point, with no action equivalence. -/
def selection (k : ℕ) (hk : 4 ≤ k)
    (U : Subgroup (Equiv.Perm (Fin (2^k))))
    [MulAction.IsPretransitive U (Fin (2^k))]
    (hcard : Nat.card U ≤ 2^(2^(k-1))) : BinaryOrderCharacterSelection U :=
  selectionOfDegree k hk U rfl hcard

section Physical

variable {h : ℕ} (k : ℕ) (hk : 4 ≤ k)
    (U : Subgroup (Equiv.Perm (Fin (2*h))))
    [MulAction.IsPretransitive U (Fin (2*h))]
    (hdegree : 2*h = 2^k) (hcard : Nat.card U ≤ 2^(2^(k-1)))

/-- Actual surviving maps receive the complete selected envelope, with
the same original normal and the same original exterior subgroup. -/
theorem original_envelope (hMaroti : NilpotentConjugacyClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal}) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b h ((selectionOfDegree k hk U hdegree hcard).prefixDegree N)
        ((selectionOfDegree k hk U hdegree hcard).liftConstant N)
        ((selectionOfDegree k hk U hdegree hcard).gapParameter N) *
          (selectionOfDegree k hk U hdegree hcard).momentWeight N J :=
  (selectionOfDegree k hk U hdegree hcard).original_envelope hMaroti hU b P N J

/-- The physical sum uses the original action's normalizer. The character
automorphism factor remains inside the selected local term. -/
theorem physical_kernel_bound (hMaroti : NilpotentConjugacyClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
      exactBenchmark (b+2*h) ≤
        ∑ N : {N : Subgroup U // N.Normal},
          (fusionMenuHotKernel (fun n => (subgroupCount n : ℝ)) b h
            ((selectionOfDegree k hk U hdegree hcard).prefixDegree N)
            ((selectionOfDegree k hk U hdegree hcard).liftConstant N)
            (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))))
            ((selectionOfDegree k hk U hdegree hcard).gapParameter N) +
          fusionColdKernel b h ((selectionOfDegree k hk U hdegree hcard).liftConstant N)
            (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))))
            (16*(selectionOfDegree k hk U hdegree hcard).gapParameter N) *
              ((subgroupCount b : ℝ)/exactBenchmark b)) :=
  (selectionOfDegree k hk U hdegree hcard).physical_kernel_bound hMaroti hU b P hP

end Physical

section FiniteMenu

variable {ι : Type*} [Fintype ι] (h k : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Fin (2*h i))))
    (hk : ∀ i, 4 ≤ k i) (hdegree : ∀ i, 2*h i = 2^(k i))
    (htrans : ∀ i, MulAction.IsPretransitive (U i) (Fin (2*h i)))
    (hcard : ∀ i, Nat.card (U i) ≤ 2^(2^(k i-1)))

/-- A fixed finite collection may contain different actual power widths. -/
def menuSelection : ∀ i, BinaryOrderCharacterSelection (U i) := by
  intro i
  letI := htrans i
  exact selectionOfDegree (k i) (hk i) (U i) (hdegree i) (hcard i)

def menuHot (n : ℕ) : ℝ :=
  fusionPhysicalMenuHot h U
    (fun i => (menuSelection h k U hk hdegree htrans hcard i).prefixDegree)
    (fun i => (menuSelection h k U hk hdegree htrans hcard i).liftConstant)
    (fun i => (menuSelection h k U hk hdegree htrans hcard i).gapParameter) n

def menuRow (n b : ℕ) : ℝ :=
  fusionPhysicalMenuRow h U
    (fun i => (menuSelection h k U hk hdegree htrans hcard i).liftConstant)
    (fun i => (menuSelection h k U hk hdegree htrans hcard i).gapParameter) n b

/-- Original physical coverage supplies the weighted recurrence. No
classification of all actions or extra normal-axis count is presumed. -/
theorem menu_recurrence (hMaroti : NilpotentConjugacyClassInput)
    (hU : ∀ i, IsPGroup 2 (U i)) (n : ℕ) (hn : ∀ i, 2*h i ≤ n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-2*h i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (U i) (hn i) (P i)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      menuHot h k U hk hdegree htrans hcard n +
        ∑ b ∈ Finset.range n, menuRow h k U hk hdegree htrans hcard n b *
          ((subgroupCount b : ℝ)/exactBenchmark b) := by
  have hh : ∀ i, 0 < h i := by
    intro i
    have hp : 0 < 2^(k i) := pow_pos (by decide : 0 < 2) _
    have hd := hdegree i
    omega
  exact binaryOrderCharacterSelection_recurrence h U
    (menuSelection h k U hk hdegree htrans hcard) hMaroti hU hh n hn F P hP hcover

theorem menu_row_contractive :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, menuRow h k U hk hdegree htrans hcard n b ≤ 1/2 := by
  apply binaryOrderCharacterSelection_row_contractive h U
    (menuSelection h k U hk hdegree htrans hcard)
  intro i
  have hp : 0 < 2^(k i) := pow_pos (by decide : 0 < 2) _
  have hd := hdegree i
  omega

theorem menu_row_decay :
    ∃ D κ : ℝ, 0<D ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, menuRow h k U hk hdegree htrans hcard n b ≤
        D*(2:ℝ)^(-κ*(n:ℝ)) := by
  apply binaryOrderCharacterSelection_row_decay h U
    (menuSelection h k U hk hdegree htrans hcard)
  intro i
  have hp : 0 < 2^(k i) := pow_pos (by decide : 0 < 2) _
  have hd := hdegree i
  omega

/-- The global coarse estimate is explicitly separate from the original
finite-action acceptance and from the conjugacy-class counting input. -/
theorem menu_hot_decay
    (hs : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ∃ D κ : ℝ, 0<D ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      menuHot h k U hk hdegree htrans hcard n ≤ D*(2:ℝ)^(-κ*(n:ℝ)^2) :=
  binaryOrderCharacterSelection_hot_decay h U
    (menuSelection h k U hk hdegree htrans hcard) hs

end FiniteMenu
end SymmetricSubgroupAsymptotics.BinaryTransitivePowerBoundaryFusion

end
