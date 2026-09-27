import SymmetricSubgroupAsymptotics.RepeatedOddMarkerStateFibre
import SymmetricSubgroupAsymptotics.RepeatedOddMarkerBinaryImageKernel

/-!
# Exact fixed-image repeated-marker model sum

The index consists of every literal invariant ternary submodule with full
coordinate projections. Each index is realized through the original section,
and each fibre consists of literal original ambient subgroups. The exact sum
uses only binaryity of the actual image B, not binaryity of the whole exterior.
No physical labelling, normalizer weight, or desired cardinal is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerModelSum

open RepeatedOddMarkerKernel RepeatedOddMarkerModule RepeatedOddMarkerSection
open RepeatedOddMarkerFibreCount

variable {ι D : Type} [Fintype ι] [Group D]
    (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D))

/-- The actual diagonal action of this same image preserves K. -/
def Invariant (K : Submodule (ZMod 3) (ι → ZMod 3)) : Prop :=
  ∀ b v, v ∈ K → DiagonalIsotypeProjection.diagonalOperator
    (TernaryDiagonalQuotientCocycles.scalar
      (RepeatedOddMarkerKernelChart.signCharacter B)) b v ∈ K

/-- Coordinate fullness does not assert independent coordinates. -/
def CoordinateFull (K : Submodule (ZMod 3) (ι → ZMod 3)) : Prop :=
  ∀ i, Function.Surjective (fun v : K => v.1 i)

abbrev AdmissibleKernel :=
  {K : Submodule (ZMod 3) (ι → ZMod 3) // Invariant B K ∧ CoordinateFull K}

/-- All original full-marker subgroups with this exact image. -/
abbrev ImageFull :=
  {H : Subgroup ((ι → OddMarkerGroup) × D) //
    H.map contraction = B ∧ ∀ i, H.map (coordinate i) = ⊤}

abbrev KernelFibre (K : Submodule (ZMod 3) (ι → ZMod 3)) :=
  FixedImageKernelSubgroupFibre contraction B (ambientKernel B K)

local instance kernelFinite : Finite (Submodule (ZMod 3) (ι → ZMod 3)) :=
  Finite.of_injective (fun K : Submodule (ZMod 3) (ι → ZMod 3) =>
    (K : Set (ι → ZMod 3))) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

/-- Literal reconstruction detects membership in precisely the selected K. -/
theorem reconstruction_mem_ambientKernel
    (K : Submodule (ZMod 3) (ι → ZMod 3)) (v : ι → ZMod 3) :
    reconstruction (D := D) (Multiplicative.ofAdd v) ∈ ambientKernel B K ↔ v ∈ K := by
  constructor
  · rintro ⟨q, ⟨a, rfl⟩, ha⟩
    change reconstruction (D := D) (Multiplicative.ofAdd a.toAdd.1) =
      reconstruction (Multiplicative.ofAdd v) at ha
    have hv : a.toAdd.1 = v := congrArg Multiplicative.toAdd
      (reconstruction_injective ha)
    exact hv ▸ a.toAdd.2
  · intro hv
    let a : Multiplicative K := Multiplicative.ofAdd ⟨v, hv⟩
    exact ⟨OriginalKernelQuotientChart.submoduleHom (pullbackProjection B)
      (RepeatedOddMarkerKernelChart.moduleRep B)
      (RepeatedOddMarkerKernelChart.originalKernelChart B) K a, ⟨a, rfl⟩, rfl⟩

/-- The fibre's literal ambient kernel is equivalent to its original
ternary kernel submodule, with no ambient normality hypothesis. -/
theorem kernel_eq_of_fibre (K : Submodule (ZMod 3) (ι → ZMod 3))
    (H : KernelFibre B K) : kernelSubmodule H.1 = K := by
  rcases H with ⟨H, hHB, hkernel⟩
  change kernelSubmodule H = K
  ext v
  rw [mem_kernelSubmodule, ← reconstruction_mem_ambientKernel B K v, ← hkernel]
  constructor
  · intro hv
    exact ⟨hv, RepeatedOddMarkerKernelChart.contraction_reconstruction
      (Multiplicative.ofAdd v)⟩
  · exact fun hv => hv.1

theorem kernel_admissible (hB : IsPGroup 2 B) (H : ImageFull B) :
    Invariant B (kernelSubmodule H.1) ∧ CoordinateFull (kernelSubmodule H.1) := by
  rcases H with ⟨H, hHB, hfull⟩
  subst B
  constructor
  · exact RepeatedOddMarkerImage.diagonal_mem H
  · intro i
    exact RepeatedOddMarkerBinaryImageKernel.coordinate_surjective H hB i (hfull i)

/-- Nontrivial original signs and full actual K-coordinates make every
member of the unrestricted fibre full in the original S3 coordinates. -/
theorem fibre_full
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1)
    (K : AdmissibleKernel B) (H : KernelFibre B K.1) :
    ∀ i, H.1.map (coordinate i) = ⊤ := by
  intro i
  apply RepeatedOddMarkerFullCoordinates.coordinate_full
  · rw [kernel_eq_of_fibre B K.1 H]
    exact K.2.2 i
  · obtain ⟨b, hb⟩ := TernarySignCocycles.exists_nontrivial_sign
      (RepeatedOddMarkerKernelChart.signCharacter B i) (hχ i)
    have hm : b.1 ∈ H.1.map contraction := by
      rw [H.2.1]
      exact b.2
    obtain ⟨h, hh, he⟩ := Subgroup.mem_map.mp hm
    refine ⟨h, hh, ?_⟩
    have hs := congrArg (fun z : (ι → Multiplicative (ZMod 2)) × D => z.1 i) he
    change oddMarkerSign (h.1 i) =
      RepeatedOddMarkerKernelChart.signCharacter B i b at hs
    rw [hs, hb]
    decide

/-- Every admissible K is realized. This is the inverse image of the
literal original section modulo its reconstructed K, not a count premise. -/
def sectionRealization (K : AdmissibleKernel B) : KernelFibre B K.1 := by
  letI : (kernelGroup B K.1).Normal := kernelGroup_normal B K.1 K.2.1
  exact (RepeatedOddMarkerFibreCount.ambientFibreEquiv B K.1).symm
    ((fixedKernelLiftEquiv (pullbackProjection B) (kernelGroup B K.1)
      (kernelGroup_le B K.1)).symm
      (quotientSectionLift B (kernelGroup B K.1) (kernelGroup_le B K.1)))

theorem sectionRealization_kernel (K : AdmissibleKernel B) :
    kernelSubmodule (sectionRealization B K).1 = K.1 :=
  kernel_eq_of_fibre B K.1 (sectionRealization B K)

def realizedImageFull
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1)
    (K : AdmissibleKernel B) : ImageFull B :=
  ⟨(sectionRealization B K).1, (sectionRealization B K).2.1,
    fibre_full B hχ K (sectionRealization B K)⟩

/-- Exact partition of actual original subgroups by their literal
admissible kernel. The inverse forgets only the proved state label. -/
def imageFullEquivSigma (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    ImageFull B ≃ Σ K : AdmissibleKernel B, KernelFibre B K.1 where
  toFun H := ⟨⟨kernelSubmodule H.1, kernel_admissible B hB H⟩,
    H.1, H.2.1, by
      change jointKernel H.1 = ambientKernel B (kernelSubmodule H.1)
      exact (RepeatedOddMarkerStateFibre.ambientKernel_eq_jointKernel H.1).symm.trans
        (congrArg (fun C => ambientKernel C (kernelSubmodule H.1)) H.2.1)⟩
  invFun z := ⟨z.2.1, z.2.2.1, fibre_full B hχ z.1 z.2⟩
  left_inv _ := rfl
  right_inv z := by
    have hk := kernel_eq_of_fibre B z.1.1 z.2
    apply Sigma.ext (Subtype.ext hk)
    have hp : ∀ H : Subgroup ((ι → OddMarkerGroup) × D),
        (H.map contraction = B ∧
          H ⊓ contraction.ker = ambientKernel B (kernelSubmodule z.2.1)) ↔
        (H.map contraction = B ∧ H ⊓ contraction.ker = ambientKernel B z.1.1) := by
      intro H
      rw [hk]
    apply (Subtype.heq_iff_coe_eq hp).mpr
    rfl

@[simp] theorem imageFullEquivSigma_symm_val (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1)
    (z : Σ K : AdmissibleKernel B, KernelFibre B K.1) :
    ((imageFullEquivSigma B hB hχ).symm z).1 = z.2.1 := rfl

private theorem kernelFibre_finite (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1)
    (K : AdmissibleKernel B) : Finite (KernelFibre B K.1) := by
  letI : Finite (TernaryDiagonalQuotientCocycles.quotientRep
      (RepeatedOddMarkerKernelChart.signCharacter B) K.1 K.2.1) := by
    change Finite ((ι → ZMod 3) ⧸ K.1)
    infer_instance
  let e := ((RepeatedOddMarkerFibreCount.ambientFibreEquiv B K.1).trans
    (fibreCocycleEquiv B K.1 K.2.1)).trans
      (TernaryDiagonalQuotientCocycles.principalEquiv
        (RepeatedOddMarkerKernelChart.signCharacter B) K.1 K.2.1 hB hχ).toEquiv.symm
  exact Finite.of_equiv _ e.symm

/-- The complete fixed-image model count over all admissible literal K.
No finite exterior or independent-coordinate assumption is needed. -/
theorem card_imageFull (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    Nat.card (ImageFull B) =
      ∑ K : AdmissibleKernel B,
        3 ^ (Fintype.card ι - Module.finrank (ZMod 3) K.1) := by
  letI (K : AdmissibleKernel B) : Finite (KernelFibre B K.1) :=
    kernelFibre_finite B hB hχ K
  rw [Nat.card_congr (imageFullEquivSigma B hB hχ), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro K _
  exact card_ambientFibre_pow B K.1 K.2.1 hB hχ

/-- The same exact model sum in the rational field used for original
physical normalizer weights. -/
theorem card_imageFull_rat (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    (Nat.card (ImageFull B) : ℚ) =
      ∑ K : AdmissibleKernel B,
        (3 : ℚ) ^ (Fintype.card ι - Module.finrank (ZMod 3) K.1) := by
  exact_mod_cast card_imageFull B hB hχ

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerModelSum

end
