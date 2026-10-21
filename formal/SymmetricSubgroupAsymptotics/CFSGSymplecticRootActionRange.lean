import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryImageAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticImageRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
import SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange

/-! The original type-C Serre model and the literal elementary matrix
group have exactly the SAME action range on the SAME integral image.
Both complete ranges are controlled by their original actual roots. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration

def elementaryRoot (K : Type*) [CommRing K] (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    elementaryRootGroup K r := ⟨rootTransvection K r neg i t, rootTransvection_mem K r neg i t⟩

def elementaryRootSet (K : Type*) [CommRing K] (r : ℕ) : Set (elementaryRootGroup K r) :=
  {u | ∃ neg i t, u = elementaryRoot K r neg i t}

theorem elementaryRootSet_generate (K : Type*) [CommRing K] (r : ℕ) :
    Subgroup.closure (elementaryRootSet K r) = ⊤ := by
  let R := Subgroup.closure (elementaryRootSet K r)
  have hmap : R.map (elementaryRootGroup K r).subtype = elementaryRootGroup K r := by
    apply le_antisymm
    · rintro u ⟨x, _, rfl⟩
      exact x.property
    · apply (Subgroup.closure_le _).mpr
      rintro u ⟨neg, i, t, rfl⟩
      exact ⟨elementaryRoot K r neg i t,
        Subgroup.subset_closure ⟨neg, i, t, rfl⟩, rfl⟩
  apply top_unique
  intro x _
  have hx : x.val ∈ R.map (elementaryRootGroup K r).subtype := by
    rw [hmap]
    exact x.property
  obtain ⟨y, hy, he⟩ := hx
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

theorem source_root_action_eq_elementary (K : Type) [Field K] (r : ℕ)
    (neg : Bool) (i : Fin r) (t : K) :
    symplecticImageRepresentation K r (modelRoot (CartanMatrix.C r).transpose K neg i t) =
      elementaryImageAction K r (elementaryRoot K r neg i t) := by
  apply LinearEquiv.ext
  intro y
  apply Subtype.ext
  exact symplecticImageRepresentation_root K r neg i t y

theorem symplectic_action_ranges_eq (K : Type) [Field K] (r : ℕ) :
    (symplecticImageRepresentation K r).range = (elementaryImageAction K r).range := by
  apply le_antisymm
  · apply CFSGGeneratedActionRange.range_le_of_generators
      (rootSet (CartanMatrix.C r).transpose K) (rootSet_generate (CartanMatrix.C r).transpose K)
      (symplecticImageRepresentation K r) (elementaryImageAction K r).range
    rintro u ⟨neg, i, t, rfl⟩
    exact ⟨elementaryRoot K r neg i t, (source_root_action_eq_elementary K r neg i t).symm⟩
  · apply CFSGGeneratedActionRange.range_le_of_generators
      (elementaryRootSet K r) (elementaryRootSet_generate K r)
      (elementaryImageAction K r) (symplecticImageRepresentation K r).range
    rintro u ⟨neg, i, t, rfl⟩
    exact ⟨modelRoot (CartanMatrix.C r).transpose K neg i t,
      source_root_action_eq_elementary K r neg i t⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
