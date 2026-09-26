import SymmetricSubgroupAsymptotics.TerminalGraphClassification
import SymmetricSubgroupAsymptotics.TerminalGaussian
import SymmetricSubgroupAsymptotics.ComplementCount
import SymmetricSubgroupAsymptotics.AbelianProductGraphClassification

/-! The terminal Gaussian weight is the exact count of binary quotient
graphs over a fixed actual exterior. Summing over all actual exterior
subgroups counts all subgroups of the original binary product exactly.
No projection onto the first factor is required to be full. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

local instance subgroupFinite {G : Type*} [Group G] [Finite G] :
    Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

local instance homFinite {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q] :
    Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- Every fixed-tail graph is counted, including proper binary projections.
Annihilator duality changes the quotient-dimension weight to the exact
Gaussian rank weight without losing or duplicating an actual subspace. -/
theorem terminalFullImages_card_eq_gaussianWeight
    (R : ℕ) (T : Type*) [Group T] [Finite T] :
    (Nat.card (TerminalFullImages (V := Fin R → ZMod 2) (T := T)) : ℝ) =
      terminalGaussianWeight R (binaryCharacterRank T) := by
  let V := Fin R → ZMod 2
  haveI (U : Submodule (ZMod 2) V) : Finite (V ⧸ U) :=
    Finite.of_surjective U.mkQ U.mkQ_surjective
  have hcard : Nat.card (TerminalFullImages (V := V) (T := T)) =
      ∑ U : Submodule (ZMod 2) V,
        2 ^ (binaryCharacterRank T * Module.finrank (ZMod 2) (V ⧸ U)) := by
    rw [Nat.card_congr (terminalGraphClassification (V := V) (T := T)),
      Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro U _
    exact binaryAbelianizationGroupHom_card T
  have hdim : Module.finrank (ZMod 2)
      (⊥ : Submodule (ZMod 2) V).dualAnnihilator = R := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq
      (⊥ : Submodule (ZMod 2) V)
    simpa only [finrank_bot, zero_add, V, Module.finrank_pi, Fintype.card_fin] using h
  have hweight :
      (∑ U : Submodule (ZMod 2) V,
        (2 : ℚ) ^ (binaryCharacterRank T * Module.finrank (ZMod 2) (V ⧸ U))) =
      ∑ j ∈ Finset.range (R + 1),
        binaryGaussianCoefficient R j * 2 ^ (binaryCharacterRank T * j) := by
    calc
      _ = ∑ U : {U : Submodule (ZMod 2) V // ⊥ ≤ U},
          (2 : ℚ) ^ (binaryCharacterRank T * Module.finrank (ZMod 2) (V ⧸ U.1)) :=
        (Fintype.sum_equiv (Equiv.subtypeUnivEquiv
          (fun U : Submodule (ZMod 2) V => (bot_le : (⊥ : Submodule (ZMod 2) V) ≤ U)))
          _ _ (fun _ => rfl)).symm
      _ = _ := by
        simpa only [hdim] using
          retainedAnnihilator_weight_sum_eq_gaussian
            (⊥ : Submodule (ZMod 2) V) (binaryCharacterRank T)
  have hq : (Nat.card (TerminalFullImages (V := V) (T := T)) : ℚ) =
      ∑ j ∈ Finset.range (R + 1),
        binaryGaussianCoefficient R j * 2 ^ (binaryCharacterRank T * j) := by
    calc
      _ = ∑ U : Submodule (ZMod 2) V,
          (2 : ℚ) ^ (binaryCharacterRank T * Module.finrank (ZMod 2) (V ⧸ U)) := by
        exact_mod_cast hcard
      _ = _ := hweight
  unfold terminalGaussianWeight
  exact_mod_cast hq

/-- The unique actual tail partitions the complete subgroup lattice.
There is no fullness condition on Y or on the binary factor. -/
theorem sum_terminalGaussianWeight_eq_subgroup_card
    (R : ℕ) (Y : Type*) [Group Y] [Finite Y] :
    (∑ H : Subgroup Y, terminalGaussianWeight R (binaryCharacterRank H)) =
      (Nat.card (Subgroup (Multiplicative (Fin R → ZMod 2) × Y)) : ℝ) := by
  have hcard : Nat.card (Subgroup (Multiplicative (Fin R → ZMod 2) × Y)) =
      ∑ H : Subgroup Y,
        Nat.card (TerminalFullImages (V := Fin R → ZMod 2) (T := H)) := by
    rw [Nat.card_congr (AbelianProductGraphClassification.tailClassification
      (E := Multiplicative (Fin R → ZMod 2)) (B := Y))]
    exact Nat.card_sigma
  calc
    _ = ∑ H : Subgroup Y,
        (Nat.card (TerminalFullImages (V := Fin R → ZMod 2) (T := H)) : ℝ) :=
      Finset.sum_congr rfl (fun H _ =>
        (terminalFullImages_card_eq_gaussianWeight R H).symm)
    _ = _ := by exact_mod_cast hcard.symm

end SymmetricSubgroupAsymptotics
