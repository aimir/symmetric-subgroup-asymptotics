import SymmetricSubgroupAsymptotics.RepeatedOddMarkerFibreCount
import SymmetricSubgroupAsymptotics.RepeatedOddMarkerFullCoordinates

/-!
# The complete exact state fibre of an original repeated-marker subgroup

All inputs to the exact count are installed from the original H: its
literal sign/exterior image, its literal reconstructed ternary kernel,
binaryity from the exterior and nontrivial signs from full S3 coordinates.
Every subgroup in this same-state fibre has full original coordinates.
Physical labelling and the weighted sum over states remain separate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerStateFibre

open RepeatedOddMarkerKernel RepeatedOddMarkerModule RepeatedOddMarkerImage
open RepeatedOddMarkerSection RepeatedOddMarkerFibreCount

variable {ι D : Type} [Fintype ι] [Group D]

private theorem jointKernel_le_of_kernel_le
    (H H' : Subgroup ((ι → OddMarkerGroup) × D))
    (hK : kernelSubmodule H ≤ kernelSubmodule H') : jointKernel H ≤ jointKernel H' := by
  intro g hg
  obtain ⟨v,hv⟩ := (RepeatedOddMarkerModule.kernelEquiv H).surjective ⟨g,hg⟩
  have he : reconstruction (Multiplicative.ofAdd v.toAdd.1)=g := congrArg Subtype.val hv
  have hm := reconstruction_mem_jointKernel H' v.toAdd.1 (hK v.toAdd.2)
  rwa [he] at hm

theorem kernel_eq_iff_jointKernel_eq (H H' : Subgroup ((ι → OddMarkerGroup) × D)) :
    kernelSubmodule H = kernelSubmodule H' ↔ jointKernel H = jointKernel H' := by
  constructor
  · intro h
    exact le_antisymm (jointKernel_le_of_kernel_le H H' h.le)
      (jointKernel_le_of_kernel_le H' H h.ge)
  · intro h
    ext v
    constructor
    · intro hv
      have hm := reconstruction_mem_jointKernel H v hv
      rw [h] at hm
      exact hm.1
    · intro hv
      have hm := reconstruction_mem_jointKernel H' v hv
      rw [← h] at hm
      exact hm.1

theorem ambientKernel_eq_jointKernel (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    ambientKernel (image H) (kernelSubmodule H) = jointKernel H := by
  apply le_antisymm
  · rintro _ ⟨q,hq,rfl⟩
    obtain ⟨v,rfl⟩ := hq
    exact reconstruction_mem_jointKernel H v.toAdd.1 v.toAdd.2
  · intro g hg
    obtain ⟨v,hv⟩ := (RepeatedOddMarkerModule.kernelEquiv H).surjective ⟨g,hg⟩
    apply Subgroup.mem_map.mpr
    refine ⟨OriginalKernelQuotientChart.submoduleHom (pullbackProjection (image H))
      (RepeatedOddMarkerKernelChart.moduleRep (image H))
      (RepeatedOddMarkerKernelChart.originalKernelChart (image H)) (kernelSubmodule H) v,
      ⟨v,rfl⟩,?_⟩
    exact congrArg Subtype.val hv

/-- Literal original subgroups with the same image and ternary kernel. -/
def Fibre (H : Subgroup ((ι → OddMarkerGroup) × D)) :=
  {H' : Subgroup ((ι → OddMarkerGroup) × D) //
    H'.map contraction = H.map contraction ∧ kernelSubmodule H' = kernelSubmodule H}

def ambientFibreEquiv (H : Subgroup ((ι → OddMarkerGroup) × D)) :
    Fibre H ≃ FixedImageKernelSubgroupFibre contraction (image H)
      (ambientKernel (image H) (kernelSubmodule H)) where
  toFun H' := ⟨H'.1,H'.2.1,by
    change jointKernel H'.1 = ambientKernel (image H) (kernelSubmodule H)
    rw [ambientKernel_eq_jointKernel]
    exact (kernel_eq_iff_jointKernel_eq H'.1 H).mp H'.2.2⟩
  invFun H' := ⟨H'.1,H'.2.1,by
    apply (kernel_eq_iff_jointKernel_eq H'.1 H).mpr
    exact H'.2.2.trans (ambientKernel_eq_jointKernel H)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fibre (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D))
    (hfull : ∀ i, H.map (coordinate i)=⊤) :
    Nat.card (Fibre H) =
      3 ^ (Fintype.card ι - Module.finrank (ZMod 3) (kernelSubmodule H)) := by
  rw [Nat.card_congr (ambientFibreEquiv H)]
  apply card_ambientFibre_pow (image H) (kernelSubmodule H)
    (RepeatedOddMarkerImage.diagonal_mem H) (image_isPGroup hD H)
  intro i hi
  obtain ⟨b,hb⟩ := RepeatedOddMarkerImage.signCharacter_nontrivial H i (hfull i)
  apply hb
  exact DFunLike.congr_fun hi b

/-- Counting the whole exact state fibre preserves every full marker
coordinate; no extra full-projection filter is silently dropped. -/
theorem full_coordinates (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D))
    (hfull : ∀ i, H.map (coordinate i)=⊤) (H' : Fibre H) :
    ∀ i, H'.1.map (coordinate i)=⊤ :=
  RepeatedOddMarkerFullCoordinates.full_of_same_state hD H H'.1
    H'.2.1.symm H'.2.2.symm hfull

/-- Finiteness follows from the exact original fibre, even when the
ambient exterior is infinite. -/
theorem finite_fibre (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D))
    (hfull : ∀ i, H.map (coordinate i)=⊤) : Finite (Fibre H) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_fibre hD H hfull]
  exact pow_ne_zero _ (by decide)

/-- Arbitrary earlier ownership exclusions remain predicates on the
original subgroup. Enlarging to the full state fibre gives an upper
bound, without asserting equality after exclusions. -/
theorem card_restricted_fibre_le (hD : IsPGroup 2 D)
    (H : Subgroup ((ι → OddMarkerGroup) × D))
    (hfull : ∀ i, H.map (coordinate i)=⊤)
    (P : Subgroup ((ι → OddMarkerGroup) × D) → Prop) :
    Nat.card {H' : Fibre H // P H'.1} ≤
      3 ^ (Fintype.card ι - Module.finrank (ZMod 3) (kernelSubmodule H)) := by
  letI := finite_fibre hD H hfull
  exact (Nat.card_le_card_of_injective
    (Subtype.val : {H' : Fibre H // P H'.1} → Fibre H) Subtype.val_injective).trans_eq
      (card_fibre hD H hfull)

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerStateFibre

end
