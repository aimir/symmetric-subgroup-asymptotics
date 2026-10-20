import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryComplete
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T22

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads

abbrev H := Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)
abbrev V := Fin 8 → ZMod 2
def generators : Fin 5 → H := closureGenerators BinaryMenuCayley8T22.generators
theorem generators_full : Subgroup.closure (Set.range generators) = ⊤ := closureGenerators_full _
def rho : Representation (ZMod 2) H V := (binaryPermutationRepresentation 8).comp H.subtype
private theorem regular_generators_agree : ∀ i : Fin 3, ∀ x,
  BinaryMenuCayley8T3.generators i x = BinaryMenuCayley8T22.generators ⟨i.val, by omega⟩ x := by decide +kernel
theorem regular_le : BinaryRegularEightNaturalRegistry.H ≤ H := by
  apply (Subgroup.closure_le H).mpr
  rintro _ ⟨i, rfl⟩
  rw [Equiv.ext (regular_generators_agree i)]
  exact Subgroup.subset_closure ⟨⟨i.val, by omega⟩, rfl⟩
def regularInclusion : BinaryRegularEightNaturalRegistry.H →* H := Subgroup.inclusion regular_le
def restrict (W : Subrepresentation rho) : Subrepresentation BinaryRegularEightNaturalRegistry.rho where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule g _ hv := W.apply_mem_toSubmodule (regularInclusion g) hv
def extraGenerator (i : Fin 2) : H := generators ⟨3 + i.val, by omega⟩
def compatible (i : Fin 47) : Prop := ∀ g : Fin 2, ∀ j : Fin (BinaryRegularEightNaturalRegistry.charts i).1,
  rho (extraGenerator g) ((BinaryRegularEightNaturalRegistry.charts i).2.inclusion (Pi.single j 1)) ∈ (BinaryRegularEightNaturalRegistry.charts i).2.space
def stateIndex : Fin 15 → Fin 47 := ![0,1,24,4,31,32,13,15,46,21,22,23,45,33,40]
def radicalIndex : Fin 15 → Fin 47 := ![0,45,33,40,33,33,23,40,40,23,23,0,33,40,23]
def headCeiling : Fin 15 → ℕ := ![0,1,1,1,1,1,1,1,1,1,1,1,2,2,2]
def charts (i : Fin 15) := BinaryRegularEightNaturalRegistry.charts (stateIndex i)
def radicalCharts (i : Fin 15) := BinaryRegularEightNaturalRegistry.charts (radicalIndex i)
private theorem positive : ∀ i g j,
  rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space := by decide +kernel
private theorem negative : ∀ i g j,
  rho (generators g)⁻¹ ((charts i).2.inclusion (Pi.single j 1)) ∈ (charts i).2.space := by decide +kernel
def states (i : Fin 15) : Subrepresentation rho :=
  (charts i).2.subrepresentationOfGenerators rho generators generators_full (positive i) (negative i)
theorem states_space (i : Fin 15) : (states i).toSubmodule = (charts i).2.space := rfl
private theorem compatible_covered : ∀ i : Fin 47, compatible i → ∃ j, stateIndex j = i := by
  unfold compatible
  decide +kernel
theorem complete (W : Subrepresentation rho) : ∃ j, states j = W := by
  obtain ⟨i, hi⟩ := BinaryRegularEightNaturalRegistry.complete (restrict W)
  have hs : (BinaryRegularEightNaturalRegistry.charts i).2.space = W.toSubmodule :=
    (BinaryRegularEightNaturalRegistry.states_space i).symm.trans (congrArg Subrepresentation.toSubmodule hi)
  have hc : compatible i := by
    intro g j
    rw [hs]
    exact W.apply_mem_toSubmodule (extraGenerator g) (hs ▸ (show
      (BinaryRegularEightNaturalRegistry.charts i).2.inclusion (Pi.single j 1) ∈ (BinaryRegularEightNaturalRegistry.charts i).2.space from ⟨_, rfl⟩))
  obtain ⟨j, hj⟩ := compatible_covered i hc
  refine ⟨j, Subrepresentation.toSubmodule_injective ?_⟩
  change (BinaryRegularEightNaturalRegistry.charts (stateIndex j)).2.space = W.toSubmodule
  rw [hj]
  exact hs
def displacementCoefficientMasks (i : Fin 15) (j : ℕ) : Array ℕ :=
  ((#[#[],#[#[1,0,0,0,0],#[9,2,1,0,0],#[11,2,1,0,0],#[9,0,1,0,0],#[1,0,1,0,0],#[33,1,0,0,0],#[1,1,0,0,0]],#[#[0,0,1,2,0],#[16,0,2,0,0],#[18,0,2,2,0],#[0,0,0,2,0],#[16,0,1,2,0]],#[#[0,1,0,0,0],#[0,3,1,0,0],#[0,1,1,0,0]],#[#[0,1,0,2,0],#[8,2,0,0,0],#[10,2,0,2,0],#[8,1,0,2,0],#[0,0,0,2,0]],#[#[2,0,0,0,2],#[8,2,0,0,0],#[8,2,0,0,2],#[10,1,0,0,2],#[2,1,0,0,2]],#[#[0,1,0,0,0]],#[#[2,2,0,0,0],#[2,0,2,0,0],#[2,2,2,0,0]],#[#[2,0,0,2,2],#[0,0,0,0,2],#[0,0,0,2,0]],#[#[0,1,0,0,0]],#[#[0,0,1,0,0]],#[],#[#[8,0,0,8,0],#[40,2,0,0,0],#[34,2,0,8,0],#[0,0,0,8,0],#[40,0,0,8,0]],#[#[0,1,0,0,0],#[2,0,1,0,0],#[0,1,1,0,0]],#[#[0,2,0,0,0]]] : Array (Array (Array ℕ)))[i.val]!)[j]!
private theorem radical_basis_mem : ∀ i j, (radicalCharts i).2.inclusion (Pi.single j 1) ∈ (charts i).2.space := by decide +kernel
theorem radical_space_le_state (i : Fin 15) : (radicalCharts i).2.space ≤ (states i).toSubmodule := (radicalCharts i).2.le_of_basis_mem _ (radical_basis_mem i)
def displacementVector (i : Fin 15) (j : Fin (radicalCharts i).1) (t : Fin 5) : (states i).toSubmodule :=
  ⟨(charts i).2.inclusion (binaryVectorOfMask _ ((displacementCoefficientMasks i j.val)[t.val]!)), ⟨_, rfl⟩⟩
private theorem radical_basis_eq : ∀ i j, (radicalCharts i).2.inclusion (Pi.single j 1) =
  ∑ t : Fin 5, (rho (generators t) (displacementVector i j t).val - (displacementVector i j t).val) := by decide +kernel
def radicalCertificate (i : Fin 15) : BinaryCoordinateDisplacementCertificate rho generators (states i) (radicalCharts i).2 where
  space_le_state := radical_space_le_state i
  termCount _ := 5
  termGenerator _ t := t
  termVector j t := displacementVector i j t
  basis_eq j := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using radical_basis_eq i j
private theorem generator_basis_mem_radical : ∀ i g j, rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) -
  (charts i).2.inclusion (Pi.single j 1) ∈ (radicalCharts i).2.space := by decide +kernel
theorem radical_eq_generatorDisplacementSpan (i : Fin 15) : representationGeneratorDisplacementSpan rho generators (states i) = (radicalCertificate i).submodule := by
  apply (radicalCertificate i).generatorDisplacementSpan_eq_of_basis_mem (charts i).2 (states_space i)
  intro g j
  change rho (generators g) ((charts i).2.inclusion (Pi.single j 1)) - (charts i).2.inclusion (Pi.single j 1) ∈ (radicalCharts i).2.space
  exact generator_basis_mem_radical i g j
theorem coinvariantsKer_map_eq_radical (i : Fin 15) : (Representation.Coinvariants.ker (states i).toRepresentation).map (states i).toSubmodule.subtype = (radicalCharts i).2.space := by
  rw [← representationGeneratorDisplacementSpan_eq_coinvariantsKer rho generators generators_full, radical_eq_generatorDisplacementSpan]
  exact (radicalCertificate i).submodule_map_subtype
private theorem codimension_le : ∀ i, (charts i).1 ≤ (radicalCharts i).1 + headCeiling i := by decide +kernel
theorem coinvariants_finrank_le (i : Fin 15) : Module.finrank (ZMod 2) (states i).toRepresentation.Coinvariants ≤ headCeiling i := by
  apply representationCoinvariants_finrank_le_of_displacementSubspace rho generators (states i) (radicalCertificate i).submodule (headCeiling i) (radicalCertificate i).le_generatorDisplacementSpan
  rw [(radicalCertificate i).finrank, states_space, (charts i).2.finrank]
  exact codimension_le i
private theorem small_headCeiling : ∀ i : Fin 15, i ≠ 12 → i ≠ 13 → i ≠ 14 → headCeiling i ≤ 1 := by decide +kernel
theorem head_gt_one_states (W : Subrepresentation rho) (hW : 1 < Module.finrank (ZMod 2) W.toRepresentation.Coinvariants) : W = states 12 ∨ W = states 13 ∨ W = states 14 := by
  obtain ⟨i, rfl⟩ := complete W
  by_cases h12 : i = 12
  · exact Or.inl (congrArg states h12)
  by_cases h13 : i = 13
  · exact Or.inr (Or.inl (congrArg states h13))
  by_cases h14 : i = 14
  · exact Or.inr (Or.inr (congrArg states h14))
  have hb := (coinvariants_finrank_le i).trans (small_headCeiling i h12 h13 h14)
  omega

end SymmetricSubgroupAsymptotics.BinaryHeisenbergEightNaturalHeads
