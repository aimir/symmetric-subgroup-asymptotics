import SymmetricSubgroupAsymptotics.BinaryCarrierTerminalFamily
import SymmetricSubgroupAsymptotics.TerminalAttachmentBound
import SymmetricSubgroupAsymptotics.BinaryTerminalHallEstimate
import SymmetricSubgroupAsymptotics.TerminalGaussianComparison

/-! Exact attachment over a specified family of original tails. Each tail
is included once, and every additional condition is tested after literal
reconstruction. The two marks in the numerical estimate belong to that
same tail; no preimage under a carrier epimorphism occurs here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryTerminalFullTailCount

open BinaryCarrierWord

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

variable {ι : Type} [Fintype ι] (a₀ : ℕ) (s : ι → Bool)
    (Y : Type) [Group Y] [Finite Y] (S : Subgroup Y → Prop)

abbrev Family (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) :=
  {K : Subgroup (CriticalProductGroup a₀ s × Y) //
    S (SubdirectTailImage.tail K) ∧ terminalCoordinatesFull a₀ s K ∧ P K}

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

/-- Unique original tail, with all other predicates evaluated after exact
inclusion into the original product. -/
theorem card_eq_sum (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) :
    Nat.card (Family a₀ s Y S P) =
      ∑ H : {H : Subgroup Y // S H},
        Nat.card {J : TerminalActualSubgroups a₀ s H.1 //
          P (J.1.map (SubdirectTailImage.inclusion H.1))} := by
  change Nat.card (SubgroupTailFibre.OriginalFamily S
    (fun K => terminalCoordinatesFull a₀ s K ∧ P K)) = _
  rw [SubgroupTailFibre.card_eq_sum]
  apply Finset.sum_congr rfl
  intro H _
  exact Nat.card_congr (fibreEquiv a₀ s Y P H.1)

theorem card_eq_sum_real (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) :
    (Nat.card (Family a₀ s Y S P) : ℝ) =
      ∑ H : {H : Subgroup Y // S H},
        (Nat.card {J : TerminalActualSubgroups a₀ s H.1 //
          P (J.1.map (SubdirectTailImage.inclusion H.1))} : ℝ) := by
  exact_mod_cast card_eq_sum a₀ s Y S P

def prefactor (R c C : ℕ) : ℝ :=
  2 * (eulerProduct⁻¹)^3 * ((R : ℝ)+1) * ((c : ℝ)+1) *
    (2 : ℝ)^(((C : ℝ)+7)^2/3)

theorem prefactor_nonneg (R c C : ℕ) : 0 ≤ prefactor R c C := by
  unfold prefactor
  positivity [euler_positive]

/-- A reusable estimate on the exact original tails. Concrete consumers
must derive these two original marks and the tail count separately. -/
theorem card_le_uniform_weight (C : ℕ)
    (hmarks : ∀ H : {H : Subgroup Y // S H},
      binaryCharacterRank H.1 + 1 ≤ C ∧
        Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H.1) ≤ C)
    (P : Subgroup (CriticalProductGroup a₀ s × Y) → Prop) :
    (Nat.card (Family a₀ s Y S P) : ℝ) ≤
      (Nat.card {H : Subgroup Y // S H} : ℝ) *
        prefactor (criticalProductRank a₀ s) (Fintype.card ι) C *
          terminalGaussianWeight (criticalProductRank a₀ s) (C-1) := by
  let R := criticalProductRank a₀ s
  let c := Fintype.card ι
  have hlocal (H : {H : Subgroup Y // S H}) :
      (Nat.card {J : TerminalActualSubgroups a₀ s H.1 //
        P (J.1.map (SubdirectTailImage.inclusion H.1))} : ℝ) ≤
          prefactor R c C * terminalGaussianWeight R (C-1) := by
    have hd : binaryCharacterRank H.1 ≤ C-1 := by
      have h := (hmarks H).1
      omega
    calc
      _ ≤ terminalGaussianDoubleSum R c (binaryCharacterRank H.1)
          (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H.1)) :=
        terminalActualSubfamily_card_le_doubleSum a₀ s H.1
          (fun J => P (J.map (SubdirectTailImage.inclusion H.1)))
      _ ≤ 2 * (eulerProduct⁻¹)^3 * (R+1) * (c+1) *
          terminalGaussianWeight R (binaryCharacterRank H.1) *
            (2 : ℝ)^(((C : ℝ)+7)^2/3) :=
        terminalGaussianDoubleSum_hall_le R c (binaryCharacterRank H.1) _ C
          (terminalCritical_two_card_le_rank a₀ s) (hmarks H).2
      _ = prefactor R c C * terminalGaussianWeight R (binaryCharacterRank H.1) := by
        unfold prefactor
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (terminalGaussianWeight_mono_right R hd) (prefactor_nonneg R c C)
  rw [card_eq_sum_real]
  calc
    _ ≤ ∑ _H : {H : Subgroup Y // S H},
        prefactor R c C * terminalGaussianWeight R (C-1) :=
      Finset.sum_le_sum fun H _ => hlocal H
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      ring

end SymmetricSubgroupAsymptotics.BinaryTerminalFullTailCount
