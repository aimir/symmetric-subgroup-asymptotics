import SymmetricSubgroupAsymptotics.BinaryCarrierTerminalFamily
import SymmetricSubgroupAsymptotics.TerminalAttachmentBound
import SymmetricSubgroupAsymptotics.BinaryTerminalHallEstimate
import SymmetricSubgroupAsymptotics.BinaryTerminalSectionalRank
import SymmetricSubgroupAsymptotics.TerminalGaussianProductIdentity
import SymmetricSubgroupAsymptotics.BinaryCyclicFourMixedHall

/-! The actual critical product is attached once to every literal subgroup
of C4^a × B. Its original individual nonabelian factors remain full, while
the whole critical projection can be proper. Additional original survival
conditions are counted as literal subfamilies. The only size input is the
actual equality |B|=2^u; both character marks and the subgroup estimate are
derived from the original groups.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCriticalCyclicFourHall

open BinaryCarrierWord

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

section Tail

variable {ι : Type} [Fintype ι] (a₀ : ℕ) (s : ι → Bool)
    (Y : Type) [Group Y] [Finite Y]

/-- Only individual original nonabelian critical coordinates are full.
Regular-coordinate fullness, or any other original condition, may be in P. -/
abbrev ActualFamily (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) :=
  {K : Subgroup (CriticalProductGroup a₀ s × Y) //
    terminalCoordinatesFull a₀ s K ∧ P K}

private def fibreEquiv
    (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) (H : Subgroup Y) :
    {J : Subgroup (CriticalProductGroup a₀ s × H) //
      J.map (MonoidHom.snd _ H) = ⊤ ∧
        terminalCoordinatesFull a₀ s (J.map (SubdirectTailImage.inclusion H)) ∧
          P (J.map (SubdirectTailImage.inclusion H))} ≃
      {J : TerminalActualSubgroups a₀ s H //
        P (J.1.map (SubdirectTailImage.inclusion H))} where
  toFun J := ⟨⟨J.1, J.2.1,
    (terminalCoordinatesFull_map_inclusion a₀ s H J.1).mp J.2.2.1⟩, J.2.2.2⟩
  invFun J := ⟨J.1.1, J.1.2.1,
    (terminalCoordinatesFull_map_inclusion a₀ s H J.1.1).mpr J.1.2.2, J.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact multiplicity: every original subgroup has its unique literal
tail H, and its original predicate is applied after exact reconstruction. -/
theorem actualFamily_card_eq_sum
    (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) :
    Nat.card (ActualFamily a₀ s Y P) =
      ∑ H : Subgroup Y, Nat.card {J : TerminalActualSubgroups a₀ s H //
        P (J.1.map (SubdirectTailImage.inclusion H))} := by
  let e : ActualFamily a₀ s Y P ≃
      SubgroupTailFibre.OriginalFamily (fun _ : Subgroup Y => True)
        (fun K => terminalCoordinatesFull a₀ s K ∧ P K) := {
    toFun := fun K => ⟨K.1, True.intro, K.2⟩
    invFun := fun K => ⟨K.1, K.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, SubgroupTailFibre.card_eq_sum]
  letI : Fintype {H : Subgroup Y // True} :=
    @Subtype.fintype (Subgroup Y) (fun _ => True)
      (fun _ => Classical.propDecidable True) (Fintype.ofFinite (Subgroup Y))
  apply Fintype.sum_equiv
    (Equiv.subtypeUnivEquiv (fun _ : Subgroup Y => True.intro))
  intro H
  exact Nat.card_congr (fibreEquiv a₀ s Y P H.1)

theorem actualFamily_card_eq_sum_real
    (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) :
    (Nat.card (ActualFamily a₀ s Y P) : ℝ) =
      ∑ H : Subgroup Y, (Nat.card {J : TerminalActualSubgroups a₀ s H //
        P (J.1.map (SubdirectTailImage.inclusion H))} : ℝ) := by
  exact_mod_cast actualFamily_card_eq_sum a₀ s Y P

end Tail

/-- Swap the binary and cyclic-four blocks, fixing the original B exactly. -/
def hallProductEquiv (R a : ℕ) (B : Type) [Group B] :
    (Multiplicative (Fin R → ZMod 2) × (Multiplicative (Fin a → ZMod 4) × B)) ≃*
      (BinaryCyclicFourSquareObstruction.Original R a × B) where
  toFun x := ((x.2.1, x.1), x.2.2)
  invFun x := (x.1.2, (x.1.1, x.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem hallProductEquiv_original (R a : ℕ) (B : Type) [Group B]
    (x : Multiplicative (Fin R → ZMod 2) × (Multiplicative (Fin a → ZMod 4) × B)) :
    (hallProductEquiv R a B x).2 = x.2.2 := rfl

/-- The full original tail sum is a subgroup count, then the checked
mixed Hall estimate applies. There is no estimate for the number of tails. -/
theorem gaussianWeight_sum_le (R a : ℕ) (B : Type) [Group B] [Finite B]
    (u : ℕ) (hB : Nat.card B = 2^u) :
    (∑ H : Subgroup (Multiplicative (Fin a → ZMod 4) × B),
      terminalGaussianWeight R (binaryCharacterRank H)) ≤
        ((a : ℝ)+1) * ((R : ℝ)+u+a+1) * (eulerProduct⁻¹)^2 *
          (2 : ℝ)^(((a : ℝ)^2+((R : ℝ)+u+a)^2)/4) := by
  rw [sum_terminalGaussianWeight_eq_subgroup_card,
    Nat.card_congr (hallProductEquiv R a B).mapSubgroup.toEquiv]
  exact BinaryCyclicFourMixedHall.mixed_subgroup_card_le R a B u hB

/-- Explicit loss for the actual critical rank R and number c of original
nonabelian critical factors. The cyclic-four number a is not a rank proxy. -/
def bound (R c a u : ℕ) : ℝ :=
  2 * (eulerProduct⁻¹)^5 * ((R : ℝ)+1) * ((c : ℝ)+1) *
    ((a : ℝ)+1) * ((R : ℝ)+u+a+1) *
      (2 : ℝ)^((((a : ℝ)+u+7)^2)/3 +
        ((a : ℝ)^2+((R : ℝ)+u+a)^2)/4)

private def terminalPrefactor (R c b : ℕ) : ℝ :=
  2 * (eulerProduct⁻¹)^3 * ((R : ℝ)+1) * ((c : ℝ)+1) *
    (2 : ℝ)^(((b : ℝ)+7)^2/3)

private theorem terminalPrefactor_nonneg (R c b : ℕ) :
    0 ≤ terminalPrefactor R c b := by
  unfold terminalPrefactor
  positivity [euler_positive]

/-- A complete actual critical-plus-C4-plus-B count. No character-rank,
cohomology, subgroup-count or finite-profile bound is an input. Arbitrary
P continues to test the original subgroup; dropping it is just inclusion. -/
theorem actualFamily_card_le
    {ι : Type} [Fintype ι] (a₀ : ℕ) (s : ι → Bool)
    (a : ℕ) (B : Type) [Group B] [Finite B]
    (u : ℕ) (hB : Nat.card B = 2^u)
    (P : Subgroup (CriticalProductGroup a₀ s ×
      (Multiplicative (Fin a → ZMod 4) × B)) → Prop) :
    (Nat.card (ActualFamily a₀ s (Multiplicative (Fin a → ZMod 4) × B) P) : ℝ) ≤
      bound (criticalProductRank a₀ s) (Fintype.card ι) a u := by
  let R := criticalProductRank a₀ s
  let c := Fintype.card ι
  let A := terminalPrefactor R c (a+u)
  have hA : 0 ≤ A := terminalPrefactor_nonneg R c (a+u)
  have hlocal (H : Subgroup (Multiplicative (Fin a → ZMod 4) × B)) :
      (Nat.card {J : TerminalActualSubgroups a₀ s H //
        P (J.1.map (SubdirectTailImage.inclusion H))} : ℝ) ≤
          A * terminalGaussianWeight R (binaryCharacterRank H) := by
    calc
      _ ≤ terminalGaussianDoubleSum R c (binaryCharacterRank H)
          (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H)) :=
        terminalActualSubfamily_card_le_doubleSum a₀ s H
          (fun J => P (J.map (SubdirectTailImage.inclusion H)))
      _ ≤ 2 * (eulerProduct⁻¹)^3 * (R+1) * (c+1) *
          terminalGaussianWeight R (binaryCharacterRank H) *
            (2 : ℝ)^((((a+u : ℕ) : ℝ)+7)^2/3) :=
        terminalGaussianDoubleSum_hall_le R c (binaryCharacterRank H) _ (a+u)
          (terminalCritical_two_card_le_rank a₀ s)
          (terminalRestrictedInflationKernel_cyclicFour_subgroup_le a B u hB.le H)
      _ = _ := by dsimp [A, terminalPrefactor]; ring
  rw [actualFamily_card_eq_sum_real]
  calc
    _ ≤ ∑ H : Subgroup (Multiplicative (Fin a → ZMod 4) × B),
        A * terminalGaussianWeight R (binaryCharacterRank H) :=
      Finset.sum_le_sum fun H _ => hlocal H
    _ = A * ∑ H : Subgroup (Multiplicative (Fin a → ZMod 4) × B),
        terminalGaussianWeight R (binaryCharacterRank H) := by rw [Finset.mul_sum]
    _ ≤ A * (((a : ℝ)+1) * ((R : ℝ)+u+a+1) * (eulerProduct⁻¹)^2 *
        (2 : ℝ)^(((a : ℝ)^2+((R : ℝ)+u+a)^2)/4)) :=
      mul_le_mul_of_nonneg_left (gaussianWeight_sum_le R a B u hB) hA
    _ = (2 * (eulerProduct⁻¹)^5 * ((R : ℝ)+1) * ((c : ℝ)+1) *
        ((a : ℝ)+1) * ((R : ℝ)+u+a+1)) *
          ((2 : ℝ)^((((a : ℝ)+u+7)^2)/3) *
            (2 : ℝ)^(((a : ℝ)^2+((R : ℝ)+u+a)^2)/4)) := by
      dsimp [A, terminalPrefactor]
      push_cast
      ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rfl

end SymmetricSubgroupAsymptotics.BinaryCriticalCyclicFourHall
