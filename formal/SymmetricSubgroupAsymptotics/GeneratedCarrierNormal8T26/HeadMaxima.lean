import SymmetricSubgroupAsymptotics.BinaryNormalRegistryHeads
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T26.Derived
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T26.RadicalProfiles

/-! Actual m-values for the complete literal 8T26 normal registry.
Generated only by export_lean_carrier_profiles_selected.py --stage heads. Every head and containment
is bound to an original subgroup; no stored carrier profile is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26
local instance headMaximaSourceGroup : Group Source := BinaryMenuCayley8T26.group

/-- Containment is computed from the checked complete original element masks. -/
def normalBelow (j i : Fin 27) : Bool :=
  decide (∀ x : Fin 64, normalMask j x = true → normalMask i x = true)

theorem normalBelow_iff (j i : Fin 27) :
    normalBelow j i = true ↔ (states j).kernel ≤ (states i).kernel := by
  simp only [normalBelow, decide_eq_true_eq]
  constructor
  · intro h x hx
    exact (normalMask_mem i x).mp (h x.index ((normalMask_mem j x).mpr hx))
  · intro h x hx
    exact (normalMask_mem i (⟨x⟩ : Source)).mpr
      (h ((normalMask_mem j (⟨x⟩ : Source)).mp hx))

def normalInDerived (j : Fin 27) : Bool := normalBelow j derivedIndex

theorem normalInDerived_iff (j : Fin 27) :
    normalInDerived j = true ↔ (states j).kernel ≤ commutator Source := by
  change normalBelow j derivedIndex = true ↔ (states j).kernel ≤ commutator Source
  simpa only [source_derived_state_eq] using normalBelow_iff j derivedIndex

/-- The finite maximum of proved heads below N and the actual derived subgroup. -/
def derivedHeadRank (i : Fin 27) : ℕ := (if i.val < 13 then (if i.val < 6 then (if i.val < 3 then (if i.val < 1 then 0 else (if i.val < 2 then 1 else 1)) else (if i.val < 4 then 1 else (if i.val < 5 then 1 else 1))) else (if i.val < 9 then (if i.val < 7 then 1 else (if i.val < 8 then 1 else 1)) else (if i.val < 11 then (if i.val < 10 then 1 else 1) else (if i.val < 12 then 2 else 2)))) else (if i.val < 20 then (if i.val < 16 then (if i.val < 14 then 2 else (if i.val < 15 then 2 else 2)) else (if i.val < 18 then (if i.val < 17 then 2 else 2) else (if i.val < 19 then 2 else 2))) else (if i.val < 23 then (if i.val < 21 then 2 else (if i.val < 22 then 2 else 2)) else (if i.val < 25 then (if i.val < 24 then 2 else 2) else (if i.val < 26 then 2 else 2)))))

private theorem derivedHeadRank_checked0 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 0 && normalInDerived j) = derivedHeadRank 0 := by
  decide +kernel

private theorem derivedHeadRank_checked1 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 1 && normalInDerived j) = derivedHeadRank 1 := by
  decide +kernel

private theorem derivedHeadRank_checked2 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 2 && normalInDerived j) = derivedHeadRank 2 := by
  decide +kernel

private theorem derivedHeadRank_checked3 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 3 && normalInDerived j) = derivedHeadRank 3 := by
  decide +kernel

private theorem derivedHeadRank_checked4 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 4 && normalInDerived j) = derivedHeadRank 4 := by
  decide +kernel

private theorem derivedHeadRank_checked5 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 5 && normalInDerived j) = derivedHeadRank 5 := by
  decide +kernel

private theorem derivedHeadRank_checked6 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 6 && normalInDerived j) = derivedHeadRank 6 := by
  decide +kernel

private theorem derivedHeadRank_checked7 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 7 && normalInDerived j) = derivedHeadRank 7 := by
  decide +kernel

private theorem derivedHeadRank_checked8 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 8 && normalInDerived j) = derivedHeadRank 8 := by
  decide +kernel

private theorem derivedHeadRank_checked9 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 9 && normalInDerived j) = derivedHeadRank 9 := by
  decide +kernel

private theorem derivedHeadRank_checked10 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 10 && normalInDerived j) = derivedHeadRank 10 := by
  decide +kernel

private theorem derivedHeadRank_checked11 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 11 && normalInDerived j) = derivedHeadRank 11 := by
  decide +kernel

private theorem derivedHeadRank_checked12 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 12 && normalInDerived j) = derivedHeadRank 12 := by
  decide +kernel

private theorem derivedHeadRank_checked13 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 13 && normalInDerived j) = derivedHeadRank 13 := by
  decide +kernel

private theorem derivedHeadRank_checked14 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 14 && normalInDerived j) = derivedHeadRank 14 := by
  decide +kernel

private theorem derivedHeadRank_checked15 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 15 && normalInDerived j) = derivedHeadRank 15 := by
  decide +kernel

private theorem derivedHeadRank_checked16 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 16 && normalInDerived j) = derivedHeadRank 16 := by
  decide +kernel

private theorem derivedHeadRank_checked17 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 17 && normalInDerived j) = derivedHeadRank 17 := by
  decide +kernel

private theorem derivedHeadRank_checked18 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 18 && normalInDerived j) = derivedHeadRank 18 := by
  decide +kernel

private theorem derivedHeadRank_checked19 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 19 && normalInDerived j) = derivedHeadRank 19 := by
  decide +kernel

private theorem derivedHeadRank_checked20 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 20 && normalInDerived j) = derivedHeadRank 20 := by
  decide +kernel

private theorem derivedHeadRank_checked21 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 21 && normalInDerived j) = derivedHeadRank 21 := by
  decide +kernel

private theorem derivedHeadRank_checked22 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 22 && normalInDerived j) = derivedHeadRank 22 := by
  decide +kernel

private theorem derivedHeadRank_checked23 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 23 && normalInDerived j) = derivedHeadRank 23 := by
  decide +kernel

private theorem derivedHeadRank_checked24 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 24 && normalInDerived j) = derivedHeadRank 24 := by
  decide +kernel

private theorem derivedHeadRank_checked25 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 25 && normalInDerived j) = derivedHeadRank 25 := by
  decide +kernel

private theorem derivedHeadRank_checked26 :
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j 26 && normalInDerived j) = derivedHeadRank 26 := by
  decide +kernel

private theorem derivedHeadRank_checked : ∀ i : Fin 27,
    normalRegistryHeadMaximum headRank
      (fun j => normalBelow j i && normalInDerived j) = derivedHeadRank i := by
  intro i
  fin_cases i
  · exact derivedHeadRank_checked0
  · exact derivedHeadRank_checked1
  · exact derivedHeadRank_checked2
  · exact derivedHeadRank_checked3
  · exact derivedHeadRank_checked4
  · exact derivedHeadRank_checked5
  · exact derivedHeadRank_checked6
  · exact derivedHeadRank_checked7
  · exact derivedHeadRank_checked8
  · exact derivedHeadRank_checked9
  · exact derivedHeadRank_checked10
  · exact derivedHeadRank_checked11
  · exact derivedHeadRank_checked12
  · exact derivedHeadRank_checked13
  · exact derivedHeadRank_checked14
  · exact derivedHeadRank_checked15
  · exact derivedHeadRank_checked16
  · exact derivedHeadRank_checked17
  · exact derivedHeadRank_checked18
  · exact derivedHeadRank_checked19
  · exact derivedHeadRank_checked20
  · exact derivedHeadRank_checked21
  · exact derivedHeadRank_checked22
  · exact derivedHeadRank_checked23
  · exact derivedHeadRank_checked24
  · exact derivedHeadRank_checked25
  · exact derivedHeadRank_checked26

theorem state_derived_head_eq (i : Fin 27) :
    primeNormalHeadMax 2 ((states i).kernel ⊓ commutator Source) = derivedHeadRank i :=
  registry.axisNormalHeadMax_eq_of_finiteMaximum source_isPGroup 2
    headRank state_head_eq normalBelow normalBelow_iff normalInDerived
    normalInDerived_iff derivedHeadRank derivedHeadRank_checked i

/-- The same m-value concerns the original literal Fin8 action and all of its
ambient-normal subgroups, transported by its specified source equivalence. -/
theorem original_derived_head_eq (i : Fin 27) :
    primeNormalHeadMax 2 (originalKernel i ⊓ commutator Original) = derivedHeadRank i :=
  (registry.axisNormalHeadMax_map_eq_finiteMaximum source_isPGroup 2
    BinaryMenuCayley8T26.originalEquiv headRank original_head_eq normalBelow
    normalBelow_iff normalInDerived normalInDerived_iff i).trans
      (derivedHeadRank_checked i)

theorem complete_original_head_maxima (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 27, originalKernel i = N ∧
      primeNormalHeadMax 2 (N ⊓ commutator Original) = derivedHeadRank i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_derived_head_eq i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26
