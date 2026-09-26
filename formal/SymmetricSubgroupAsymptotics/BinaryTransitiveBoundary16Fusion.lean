import SymmetricSubgroupAsymptotics.BinaryOrderPrunedNontrivialAxes
import SymmetricSubgroupAsymptotics.BinaryTransitiveCentralCriterion
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterFusion

/-! Uniform complete normal-axis choices for original transitive actions
on sixteen points of order at most 256. Small sources use order throughout;
otherwise only the literal trivial normal uses the character criterion.
No finite group list or individual normal-subgroup table is required.
The physical counting theorem retains the named class-count input.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryTransitiveBoundary16Fusion

variable (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)]

/-- The same original normal is retained in each alternative. The choice
is made before selecting any exterior degree, subgroup or survival rule. -/
def selection (hcard : Nat.card U ≤ 256) : BinaryOrderCharacterSelection U := by
  rintro ⟨N, hNormal⟩
  letI := hNormal
  by_cases hsmall : Nat.card U ≤ 128
  · exact .inl (BinaryOrderPrunedCoverage.certificateOfCard (a := 7)
      U N hsmall (by decide))
  · by_cases hN : N = ⊥
    · subst N
      have hlarge : 16 < Nat.card U := by omega
      exact .inr (binaryTransitiveSixteen_botCharacterCriterion U hlarge)
    · exact .inl (BinaryOrderPrunedNontrivialAxes.sixteenCertificate U N hcard hN)

/-- Even the largest chosen order marker has degree at most fourteen;
the character alternative has marker degree zero. -/
theorem selection_prefixDegree_le (hcard : Nat.card U ≤ 256)
    (N : {N : Subgroup U // N.Normal}) :
    (selection U hcard).prefixDegree N ≤ 14 := by
  change ((selection U hcard) N).prefixDegree ≤ 14
  cases hC : (selection U hcard) N with
  | inl C =>
    change 2 * Nat.log 2 (Nat.card (U ⧸ N.1)) ≤ 14
    have h := C.gap
    omega
  | inr C => exact Nat.zero_le _

/-- Every actual surviving map on every original normal axis receives
its selected bound. There is no omitted-axis or exclusion premise. -/
theorem original_envelope (hMaroti : NilpotentConjugacyClassInput)
    (hU : IsPGroup 2 U) (hcard : Nat.card U ≤ 256) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal}) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b 8 ((selection U hcard).prefixDegree N)
        ((selection U hcard).liftConstant N) ((selection U hcard).gapParameter N) *
          (selection U hcard).momentWeight N J :=
  (selection U hcard).original_envelope (h := 8) hMaroti hU b P N J

/-- Complete original-normalizer physical bound for a bounded-order
transitive source. Original survival and physical naturality are retained. -/
theorem physical_kernel_bound (hMaroti : NilpotentConjugacyClassInput)
    (hU : IsPGroup 2 U) (hcard : Nat.card U ≤ 256) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
      exactBenchmark (b+16) ≤
        ∑ N : {N : Subgroup U // N.Normal},
          (fusionMenuHotKernel (fun n => (subgroupCount n : ℝ)) b 8
            ((selection U hcard).prefixDegree N) ((selection U hcard).liftConstant N)
            (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 16)))))
            ((selection U hcard).gapParameter N) +
          fusionColdKernel b 8 ((selection U hcard).liftConstant N)
            (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin 16)))))
            (16*(selection U hcard).gapParameter N) *
              ((subgroupCount b : ℝ)/exactBenchmark b)) :=
  (selection U hcard).physical_kernel_bound (h := 8) hMaroti hU b P hP

section FiniteMenu

variable {ι : Type*} [Fintype ι]
    (A : ι → Subgroup (Equiv.Perm (Fin 16)))
    (htrans : ∀ i, MulAction.IsPretransitive (A i) (Fin 16))
    (hcard : ∀ i, Nat.card (A i) ≤ 256)

/-- All literal normals of every fixed original action receive their
uniform certificate before any exterior or physical family is chosen. -/
def menuSelection : ∀ i, BinaryOrderCharacterSelection (A i) := by
  intro i
  letI := htrans i
  exact selection (A i) (hcard i)

/-- The actual finite hot sum, retaining the original action normalizer
for each source and the complete original normal-axis multiplicity. -/
def menuHot (n : ℕ) : ℝ :=
  fusionPhysicalMenuHot (fun _ : ι => 8) A
    (fun i => (menuSelection A htrans hcard i).prefixDegree)
    (fun i => (menuSelection A htrans hcard i).liftConstant)
    (fun i => (menuSelection A htrans hcard i).gapParameter) n

/-- The same complete finite family gives its original weighted
continuation row, rather than a count of certificate labels. -/
def menuRow (n b : ℕ) : ℝ :=
  fusionPhysicalMenuRow (fun _ : ι => 8) A
    (fun i => (menuSelection A htrans hcard i).liftConstant)
    (fun i => (menuSelection A htrans hcard i).gapParameter) n b

/-- A complete actual finite cover by order-at-most-256 transitive
degree-sixteen actions supplies the original weighted recurrence. The
source binary hypotheses, class input and physical naturality are explicit. -/
theorem menu_recurrence (hMaroti : NilpotentConjugacyClassInput)
    (hU : ∀ i, IsPGroup 2 (A i)) (n : ℕ) (hn : 16 ≤ n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (A i × Equiv.Perm (Fin (n-16))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (A i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionCanonicalFamily (h := 8) (A i) hn (P i)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      menuHot A htrans hcard n +
        ∑ b ∈ Finset.range n, menuRow A htrans hcard n b *
          ((subgroupCount b : ℝ)/exactBenchmark b) :=
  binaryOrderCharacterSelection_recurrence (fun _ : ι => 8) A
    (menuSelection A htrans hcard) hMaroti hU (fun _ => by change 0 < 8; decide)
    n (fun _ => hn) F P hP hcover

/-- The fixed original finite continuation row eventually contracts,
without a premise bounding total subgroup counts. -/
theorem menu_row_contractive :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, menuRow A htrans hcard n b ≤ 1/2 :=
  binaryOrderCharacterSelection_row_contractive (fun _ : ι => 8) A
    (menuSelection A htrans hcard) (fun _ => by change 0 < 8; decide)

theorem menu_row_decay :
    ∃ D κ : ℝ, 0<D ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, menuRow A htrans hcard n b ≤ D*(2:ℝ)^(-κ*(n:ℝ)) :=
  binaryOrderCharacterSelection_row_decay (fun _ : ι => 8) A
    (menuSelection A htrans hcard) (fun _ => by change 0 < 8; decide)

/-- Hot decay uses the explicit global coarse input. Finite action
acceptance and the character class input do not prove that global input. -/
theorem menu_hot_decay
    (hs : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ∃ D κ : ℝ, 0<D ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      menuHot A htrans hcard n ≤ D*(2:ℝ)^(-κ*(n:ℝ)^2) :=
  binaryOrderCharacterSelection_hot_decay (fun _ : ι => 8) A
    (menuSelection A htrans hcard) hs

end FiniteMenu

/-- The complete finite collection of literal accepted actions on the
original sixteen points. This subtype needs no action-registry enumeration. -/
abbrev BoundaryAction :=
  {A : Subgroup (Equiv.Perm (Fin 16)) //
    IsPGroup 2 A ∧ MulAction.IsPretransitive A (Fin 16) ∧ Nat.card A ≤ 256}

instance boundaryActionFintype : Fintype BoundaryAction := Fintype.ofFinite _

def boundaryAction (i : BoundaryAction) : Subgroup (Equiv.Perm (Fin 16)) := i.1

theorem boundaryAction_isPGroup (i : BoundaryAction) : IsPGroup 2 (boundaryAction i) :=
  i.2.1

theorem boundaryAction_transitive (i : BoundaryAction) :
    MulAction.IsPretransitive (boundaryAction i) (Fin 16) := i.2.2.1

theorem boundaryAction_card_le (i : BoundaryAction) : Nat.card (boundaryAction i) ≤ 256 :=
  i.2.2.2

def allActionsHot (n : ℕ) : ℝ :=
  menuHot boundaryAction boundaryAction_transitive boundaryAction_card_le n

def allActionsRow (n b : ℕ) : ℝ :=
  menuRow boundaryAction boundaryAction_transitive boundaryAction_card_le n b

/-- Canonical complete accepted-action aggregate. The cover remains a
literal physical membership hypothesis; no numerical count is assumed. -/
theorem all_actions_recurrence (hMaroti : NilpotentConjugacyClassInput)
    (n : ℕ) (hn : 16 ≤ n) (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i : BoundaryAction,
      Subgroup (boundaryAction i × Equiv.Perm (Fin (n-16))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (boundaryAction i) (P i))
    (hcover : ∀ H∈F, ∃ i : BoundaryAction,
      H∈FusionCanonicalFamily (h := 8) (boundaryAction i) hn (P i)) :
    (Nat.card F : ℝ)/exactBenchmark n ≤ allActionsHot n +
      ∑ b ∈ Finset.range n, allActionsRow n b *
        ((subgroupCount b : ℝ)/exactBenchmark b) :=
  menu_recurrence boundaryAction boundaryAction_transitive boundaryAction_card_le
    hMaroti boundaryAction_isPGroup n hn F P hP hcover

theorem all_actions_row_contractive :
    ∀ᶠ n : ℕ in atTop, ∑ b ∈ Finset.range n, allActionsRow n b ≤ 1/2 :=
  menu_row_contractive boundaryAction boundaryAction_transitive boundaryAction_card_le

theorem all_actions_row_decay :
    ∃ D κ : ℝ, 0<D ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, allActionsRow n b ≤ D*(2:ℝ)^(-κ*(n:ℝ)) :=
  menu_row_decay boundaryAction boundaryAction_transitive boundaryAction_card_le

theorem all_actions_hot_decay
    (hs : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    ∃ D κ : ℝ, 0<D ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      allActionsHot n ≤ D*(2:ℝ)^(-κ*(n:ℝ)^2) :=
  menu_hot_decay boundaryAction boundaryAction_transitive boundaryAction_card_le hs

end SymmetricSubgroupAsymptotics.BinaryTransitiveBoundary16Fusion

end
