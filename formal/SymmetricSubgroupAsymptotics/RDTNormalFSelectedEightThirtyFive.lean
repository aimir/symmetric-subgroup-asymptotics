import SymmetricSubgroupAsymptotics.NormalFGeneratorBounds
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.Derived
import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalFMarkedPeel

/-! One original degree-eight proper-normal-F packet. Its mixed
commutator and centralizer are bounded in the same original carrier. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.RDTNormalFSelectedEightThirtyFive
open BinaryCarrierNormal8T35
open MarkedC4.RDTNormalFInterface MarkedC4.ActualNormalFMarkedPeel
local instance : Group Source := BinaryMenuCayley8T35.group

private theorem mixed_generator_checks : ∀ i j,
    ⁅N12.normalGenerators i,generators j⁆∈N2.kernel := by
  intro i j
  apply (normalMask_mem 2 _).mp
  revert i j
  decide +kernel

theorem mixed_commutator_le : targetCommutator N12.kernel≤N2.kernel := by
  change ⁅N12.kernel,⊤⁆≤N2.kernel
  rw [←generators_full]
  exact mixedCommutator_le_of_generator_checks N12.normalGenerators generators
    N2.kernel mixed_generator_checks

private theorem centralizer_checks : ∀ i : Fin 128,
    (∀ j, N12.normalGenerators j*(⟨i⟩ : Source)=
      (⟨i⟩ : Source)*N12.normalGenerators j) → normalMask 2 i=true := by
  decide +kernel

theorem centralizer_le : targetCentralizer N12.kernel≤N2.kernel := by
  intro x hx
  apply (normalMask_mem 2 x).mp
  apply centralizer_checks x.index
  intro j
  exact Subgroup.mem_centralizer_iff.mp hx (N12.normalGenerators j)
    (Subgroup.subset_closure (Set.mem_range_self j))

theorem retained_card_bounds :
    Nat.card (targetCommutator N12.kernel)≤4 ∧
      Nat.card (targetCentralizer N12.kernel)≤4 := by
  constructor
  · calc
      _ ≤ Nat.card N2.kernel := Nat.card_le_card_of_injective
        (Subgroup.inclusion mixed_commutator_le)
        (Subgroup.inclusion_injective mixed_commutator_le)
      _ = 4 := N2.kernel_card
  · calc
      _ ≤ Nat.card N2.kernel := Nat.card_le_card_of_injective
        (Subgroup.inclusion centralizer_le)
        (Subgroup.inclusion_injective centralizer_le)
      _ = 4 := N2.kernel_card

/-- A proper original normal subgroup supplies the common excess-one
budget; using the whole group here would give the false bound 4+1≤4. -/
theorem retained_log_bounds :
    commutatorLog N12.kernel+centralLog N12.kernel≤4 ∧
      centralLog N12.kernel≤2 := by
  have log_le_two (T : Subgroup Source) (hT : Nat.card T≤4) :
      Real.logb 2 (Nat.card T : ℝ)≤2 := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
      (by exact_mod_cast Nat.card_pos (α := T))).mpr
    norm_num
    exact_mod_cast hT
  have hc := log_le_two _ retained_card_bounds.1
  have hz := log_le_two _ retained_card_bounds.2
  refine ⟨?_,hz⟩
  change Real.logb 2 (Nat.card (targetCommutator N12.kernel) : ℝ)+
    Real.logb 2 (Nat.card (targetCentralizer N12.kernel) : ℝ)≤4
  linarith

end SymmetricSubgroupAsymptotics.RDTNormalFSelectedEightThirtyFive
