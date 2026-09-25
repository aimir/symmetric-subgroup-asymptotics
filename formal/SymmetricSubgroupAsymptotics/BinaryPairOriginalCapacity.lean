import SymmetricSubgroupAsymptotics.BinaryPairSubgroupCuts

/-! Original-group certificate interface for central cuts of pair sections.
All commutators are computed in U and its literal pair kernel. Capacity
is returned for the original quotient U/(K∨N), by surjective inflation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I ι : Type}
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
    (N : Subgroup U) [N.Normal]
    (generators : ι→U) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (L : Subgroup F.top.ker)
    (hcomm : ∀ j, ∀ k : L, (k:F.top.ker)⁻¹*MulAut.conjNormal
      (generators j) (k:F.top.ker)∈(F.sectionMap N).ker)

include hgen hcomm in
theorem originalCut_fixed : sectionSubgroupImage (p := 2) (F.sectionMap N) L≤
    (F.sectionRepresentation N).invariants := by
  have h := sectionSubgroupImage_le_invariants_of_generators (F.sectionMap N)
    ((F.sectionRepresentation N).comp (QuotientGroup.mk' (F.top.ker⊔N)))
    (MulAut.conjNormal (H := F.top.ker))
    (F.sectionRepresentation_apply N) generators hgen L hcomm
  intro v hv g
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (F.top.ker⊔N) g
  exact h hv u

def originalCutRepresentation : Representation (ZMod 2) (U ⧸ (F.top.ker⊔N))
    ((F.kernelSpace ⧸ F.normalSpace N) ⧸ sectionSubgroupImage (p := 2) (F.sectionMap N) L) :=
  F.cutRepresentation N (sectionSubgroupImage (p := 2) (F.sectionMap N) L)
    (F.originalCut_fixed N generators hgen L hcomm)

@[simp] theorem originalCutRepresentation_apply (u : U) (k : F.top.ker) :
    F.originalCutRepresentation N generators hgen L hcomm
      (QuotientGroup.mk' (F.top.ker⊔N) u)
      (sectionSubgroupCutMap (p := 2) (F.sectionMap N) L k).toAdd =
        (sectionSubgroupCutMap (p := 2) (F.sectionMap N) L (MulAut.conjNormal u k)).toAdd :=
  normalSectionCutRepresentation_apply F.top.ker N (F.sectionMap N)
    (F.sectionMap_surjective N) (F.sectionMap_ker N)
    (sectionSubgroupImage (p := 2) (F.sectionMap N) L)
    (F.originalCut_fixed N generators hgen L hcomm) u k

/-- The complete fixed preimage is a subgroup of the original pair
kernel, tested using the original group action. -/
def originalCutFixedPreimage : Subgroup F.top.ker :=
  sectionSubspacePreimage (sectionSubgroupCutMap (p := 2) (F.sectionMap N) L)
    (Representation.invariants ((F.originalCutRepresentation N generators hgen L hcomm).comp
      (QuotientGroup.mk' (F.top.ker⊔N))))

theorem originalCutFixedPreimage_mem_iff (hL : (F.sectionMap N).ker≤L)
    (k : F.top.ker) :
    k∈F.originalCutFixedPreimage N generators hgen L hcomm ↔
      ∀ j, k⁻¹*MulAut.conjNormal (generators j) k∈L := by
  rw [originalCutFixedPreimage,sectionFixedPreimage_mem_iff_generators
    (sectionSubgroupCutMap (p := 2) (F.sectionMap N) L)
    ((F.originalCutRepresentation N generators hgen L hcomm).comp
      (QuotientGroup.mk' (F.top.ker⊔N))) (MulAut.conjNormal (H := F.top.ker))
    (F.originalCutRepresentation_apply N generators hgen L hcomm) generators hgen,
    sectionSubgroupCutMap_ker (F.sectionMap N) L hL]

/-- Checked orders of two literal kernel subgroups prove the exact Schur
capacity for the retained original quotient and its retained central cut. -/
theorem originalCut_capacity_of_card [Finite X] [Finite I] (hU : IsPGroup 2 U)
    (hL : (F.sectionMap N).ker≤L) (r : ℕ)
    (hcard : Nat.card (F.originalCutFixedPreimage N generators hgen L hcomm)=
      Nat.card L*2^r) :
    representationSchurCapacity (F.originalCutRepresentation N generators hgen L hcomm)=(r:ℝ) := by
  letI : Finite ((F.kernelSpace ⧸ F.normalSpace N) ⧸ sectionSubgroupImage (p := 2) (F.sectionMap N) L) :=
    Finite.of_surjective (fun k => (sectionSubgroupCutMap (p := 2) (F.sectionMap N) L k).toAdd)
      (Multiplicative.toAdd.surjective.comp (sectionSubgroupCutMap_surjective
        (F.sectionMap N) (F.sectionMap_surjective N) L))
  have hc := binary_section_capacity_of_card
    (sectionSubgroupCutMap (p := 2) (F.sectionMap N) L)
    (sectionSubgroupCutMap_surjective (F.sectionMap N) (F.sectionMap_surjective N) L)
    ((F.originalCutRepresentation N generators hgen L hcomm).comp
      (QuotientGroup.mk' (F.top.ker⊔N))) hU r (by
      rw [sectionSubgroupCutMap_ker (F.sectionMap N) L hL]
      exact hcard)
  rwa [representationSchurCapacity_comp _ (QuotientGroup.mk'_surjective _) _] at hc

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
