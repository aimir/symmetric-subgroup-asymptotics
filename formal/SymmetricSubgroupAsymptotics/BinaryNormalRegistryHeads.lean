import SymmetricSubgroupAsymptotics.BinaryNormalSparseRegistry
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank

/-! Exact ambient-normal head maxima from a complete literal registry.
Finite head values and containment masks must be proved on the original
states. Registry completeness supplies every original normal subgroup;
no stored profile or normal-head maximum is accepted as an assumption. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- A finite numerical maximum with a decidable, explicitly checked mask.
Repeated registry states do not affect the supremum. -/
def normalRegistryHeadMaximum {I : Type*} [Fintype I]
    (heads : I → ℕ) (eligible : I → Bool) : ℕ :=
  (Finset.univ.filter (fun i => eligible i = true)).sup heads

namespace BinaryNormalSparseRegistry

variable {G ι I : Type*} [Group G] [Finite G] [Fintype I]
    {generators : ι → G} {hgen : Subgroup.closure (Set.range generators) = ⊤}
    {states : I → BinaryNormalState generators}
    (C : BinaryNormalSparseRegistry hgen states) (hG : IsPGroup 2 G)
    (p : ℕ) [Fact p.Prime]

include C hG

/-- Completeness turns a finite maximum into the maximum over all
whole-G-normal subgroups below the same actual S. S need not be normal. -/
theorem normalHeadMax_eq_finiteMaximum (S : Subgroup G)
    (heads : I → ℕ)
    (hheads : ∀ i, Module.finrank (ZMod p)
      (primeRelativeCharacters p (states i).kernel) = heads i)
    (eligible : I → Bool)
    (heligible : ∀ i, eligible i = true ↔ (states i).kernel ≤ S) :
    primeNormalHeadMax p S = normalRegistryHeadMaximum heads eligible := by
  classical
  apply le_antisymm
  · apply (primeNormalHeadMax_le_iff p S _).mpr
    intro M _ hM
    obtain ⟨i, rfl⟩ := C.complete hG M
    rw [hheads i]
    exact Finset.le_sup (f := heads)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (heligible i).mpr hM⟩)
  · unfold normalRegistryHeadMaximum
    apply Finset.sup_le_iff.mpr
    intro i hi
    rw [← hheads i]
    exact primeRelativeHead_le_normalHeadMax p S (states i).kernel
      ((heligible i).mp (Finset.mem_filter.mp hi).2)

/-- Every state's actual m-value is computed using containment in both
that state and the original ambient derived subgroup. Normality always
means normality in G, not merely in the selected state or in G'. -/
theorem axisNormalHeadMax_eq_finiteMaximum
    (heads : I → ℕ)
    (hheads : ∀ i, Module.finrank (ZMod p)
      (primeRelativeCharacters p (states i).kernel) = heads i)
    (below : I → I → Bool)
    (hbelow : ∀ j i, below j i = true ↔ (states j).kernel ≤ (states i).kernel)
    (inDerived : I → Bool)
    (hderived : ∀ j, inDerived j = true ↔ (states j).kernel ≤ commutator G)
    (i : I) :
    primeNormalHeadMax p ((states i).kernel ⊓ commutator G) =
      normalRegistryHeadMaximum heads (fun j => below j i && inDerived j) := by
  apply C.normalHeadMax_eq_finiteMaximum hG p _ heads hheads
  intro j
  simp [hbelow j i, hderived j, le_inf_iff]

/-- A checked finite supremum binds the supplied numerical m-column to
the actual subgroup invariant. The final input is only finite arithmetic,
after all original heads and containment equivalences have been proved. -/
theorem axisNormalHeadMax_eq_of_finiteMaximum
    (heads : I → ℕ)
    (hheads : ∀ i, Module.finrank (ZMod p)
      (primeRelativeCharacters p (states i).kernel) = heads i)
    (below : I → I → Bool)
    (hbelow : ∀ j i, below j i = true ↔ (states j).kernel ≤ (states i).kernel)
    (inDerived : I → Bool)
    (hderived : ∀ j, inDerived j = true ↔ (states j).kernel ≤ commutator G)
    (values : I → ℕ)
    (hvalues : ∀ i,
      normalRegistryHeadMaximum heads (fun j => below j i && inDerived j) = values i)
    (i : I) :
    primeNormalHeadMax p ((states i).kernel ⊓ commutator G) = values i :=
  (C.axisNormalHeadMax_eq_finiteMaximum hG p heads hheads below hbelow
    inDerived hderived i).trans (hvalues i)

section Mapped

variable {H : Type*} [Group H] [Finite H] (e : G ≃* H)

local instance mappedKernel_normal (i : I) :
    ((states i).kernel.map e.toMonoidHom).Normal :=
  Subgroup.Normal.map (states i).normal _ e.surjective

/-- The same complete registry computes a maximum on the literal mapped
subgroups under a specified original-group equivalence. Head equations
are required in that target ambient group, preserving its conjugation. -/
theorem normalHeadMax_map_eq_finiteMaximum (S : Subgroup H)
    (heads : I → ℕ)
    (hheads : ∀ i, Module.finrank (ZMod p)
      (primeRelativeCharacters p ((states i).kernel.map e.toMonoidHom)) = heads i)
    (eligible : I → Bool)
    (heligible : ∀ i, eligible i = true ↔
      (states i).kernel.map e.toMonoidHom ≤ S) :
    primeNormalHeadMax p S = normalRegistryHeadMaximum heads eligible := by
  classical
  apply le_antisymm
  · apply (primeNormalHeadMax_le_iff p S _).mpr
    intro M _ hM
    obtain ⟨i, rfl⟩ := C.complete_map_of_equiv hG e M
    rw [hheads i]
    exact Finset.le_sup (f := heads)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (heligible i).mpr hM⟩)
  · unfold normalRegistryHeadMaximum
    apply Finset.sup_le_iff.mpr
    intro i hi
    rw [← hheads i]
    exact primeRelativeHead_le_normalHeadMax p S
      ((states i).kernel.map e.toMonoidHom)
      ((heligible i).mp (Finset.mem_filter.mp hi).2)

/-- Source containment masks transport exactly under the given equivalence.
The target maximum is over all target-ambient normals below the mapped
state's intersection with the target's actual derived subgroup. -/
theorem axisNormalHeadMax_map_eq_finiteMaximum
    (heads : I → ℕ)
    (hheads : ∀ i, Module.finrank (ZMod p)
      (primeRelativeCharacters p ((states i).kernel.map e.toMonoidHom)) = heads i)
    (below : I → I → Bool)
    (hbelow : ∀ j i, below j i = true ↔ (states j).kernel ≤ (states i).kernel)
    (inDerived : I → Bool)
    (hderived : ∀ j, inDerived j = true ↔ (states j).kernel ≤ commutator G)
    (i : I) :
    primeNormalHeadMax p
        ((states i).kernel.map e.toMonoidHom ⊓ commutator H) =
      normalRegistryHeadMaximum heads (fun j => below j i && inDerived j) := by
  have hcomm : (commutator G).map e.toMonoidHom = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective, ← commutator_def]
  apply C.normalHeadMax_map_eq_finiteMaximum hG p e _ heads hheads
  intro j
  simp only [Bool.and_eq_true_iff, hbelow j i, hderived j, le_inf_iff, ← hcomm,
    Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective]

end Mapped

end BinaryNormalSparseRegistry
end SymmetricSubgroupAsymptotics
