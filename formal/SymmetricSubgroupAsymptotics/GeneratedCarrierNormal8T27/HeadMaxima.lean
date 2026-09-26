import SymmetricSubgroupAsymptotics.BinaryNormalRegistryHeads
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.Derived
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.RadicalProfiles

/-! Actual m-values for the complete literal J=8T27 normal registry.
Generated only by export_lean_carrier_j_heads.py. Every head and containment
is bound to an original subgroup; no stored carrier profile is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
local instance headMaximaSourceGroup : Group Source := BinaryMenuCayley8T27.group

/-- Containment is computed from the checked complete original element masks. -/
def normalBelow (j i : Fin 13) : Bool :=
  decide (∀ x : Fin 64, normalMask j x = true → normalMask i x = true)

theorem normalBelow_iff (j i : Fin 13) :
    normalBelow j i = true ↔ (states j).kernel ≤ (states i).kernel := by
  simp only [normalBelow, decide_eq_true_eq]
  constructor
  · intro h x hx
    exact (normalMask_mem i x).mp (h x.index ((normalMask_mem j x).mpr hx))
  · intro h x hx
    exact (normalMask_mem i (⟨x⟩ : Source)).mpr
      (h ((normalMask_mem j (⟨x⟩ : Source)).mp hx))

def normalInDerived (j : Fin 13) : Bool := normalBelow j 4

theorem normalInDerived_iff (j : Fin 13) :
    normalInDerived j = true ↔ (states j).kernel ≤ commutator Source := by
  change normalBelow j 4 = true ↔ (states j).kernel ≤ commutator Source
  simpa only [source_derived_eq] using normalBelow_iff j 4

/-- The finite maximum of proved heads below N and the actual derived subgroup. -/
def derivedHeadRank (i : Fin 13) : ℕ := (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 1)) else (if i.val < 4 then 1 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 1 else 1)) else (if i.val < 11 then (if i.val < 10 then 1 else 1) else (if i.val < 12 then 1 else 1))))

private theorem derivedHeadRank_checked : ∀ i : Fin 13,
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j i && normalInDerived j) = derivedHeadRank i := by
  intro i
  fin_cases i <;> decide +kernel

theorem state_derived_head_eq (i : Fin 13) :
    primeNormalHeadMax 2 ((states i).kernel ⊓ commutator Source) = derivedHeadRank i :=
  registry.axisNormalHeadMax_eq_of_finiteMaximum source_isPGroup 2
    headRank state_head_eq normalBelow normalBelow_iff normalInDerived
    normalInDerived_iff derivedHeadRank derivedHeadRank_checked i

/-- The same m-value concerns the original literal Fin8 action and all of its
ambient-normal subgroups, transported by its specified source equivalence. -/
theorem original_derived_head_eq (i : Fin 13) :
    primeNormalHeadMax 2 (originalKernel i ⊓ commutator Original) = derivedHeadRank i :=
  (registry.axisNormalHeadMax_map_eq_finiteMaximum source_isPGroup 2
    BinaryMenuCayley8T27.originalEquiv headRank original_head_eq normalBelow
    normalBelow_iff normalInDerived normalInDerived_iff i).trans
      (derivedHeadRank_checked i)

theorem complete_original_head_maxima (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 13, originalKernel i = N ∧
      primeNormalHeadMax 2 (N ⊓ commutator Original) = derivedHeadRank i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_derived_head_eq i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
