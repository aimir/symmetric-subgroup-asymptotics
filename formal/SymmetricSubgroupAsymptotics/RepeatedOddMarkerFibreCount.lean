import SymmetricSubgroupAsymptotics.RepeatedOddMarkerKernelChart
import SymmetricSubgroupAsymptotics.OriginalKernelQuotientChart
import SymmetricSubgroupAsymptotics.ImageKernelSubgroupFibres

/-!
# Exact repeated-marker fibres with the original image and kernel

Fix the literal sign/exterior image B and a literal invariant ternary
submodule K. Quotienting the actual pullback by its reconstructed K gives
the exact original kernel module V/K. The fixed-kernel subgroup fibre is
equivalent to its full cocycle space, using the explicit original section.

If B is binary and every original coordinate sign is nontrivial, the
checked diagonal quotient theorem gives exactly |V/K| subgroups. Equal
signs and all correlations inside K remain intact. The ambient version
decodes each subgroup through the actual pullback inclusion. No physical
weight, relabelling invariance, or numerical count is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerFibreCount

open groupCohomology RepeatedOddMarkerKernel RepeatedOddMarkerSection

variable {ι D : Type} [Fintype ι] [Group D]
    (B : Subgroup ((ι → Multiplicative (ZMod 2)) × D))
    (K : Submodule (ZMod 3) (ι → ZMod 3))

/-- The exact reconstructed group inside the original pullback. -/
def kernelGroup : Subgroup (pullback B) :=
  OriginalKernelQuotientChart.submoduleGroup (pullbackProjection B)
    (RepeatedOddMarkerKernelChart.moduleRep B)
    (RepeatedOddMarkerKernelChart.originalKernelChart B) K

theorem kernelGroup_le : kernelGroup B K ≤ (pullbackProjection B).ker :=
  OriginalKernelQuotientChart.submoduleGroup_le_kernel (pullbackProjection B)
    (RepeatedOddMarkerKernelChart.moduleRep B)
    (RepeatedOddMarkerKernelChart.originalKernelChart B) K

variable (hK : ∀ b v, v ∈ K →
  DiagonalIsotypeProjection.diagonalOperator
    (TernaryDiagonalQuotientCocycles.scalar (RepeatedOddMarkerKernelChart.signCharacter B)) b v ∈ K)

private def stable : ∀ b, K ≤ K.comap ((RepeatedOddMarkerKernelChart.moduleRep B).ρ b) :=
  fun b _ hv => hK b _ hv

include hK in
theorem kernelGroup_normal : (kernelGroup B K).Normal :=
  OriginalKernelQuotientChart.submoduleGroup_normal (pullbackProjection B)
    (RepeatedOddMarkerKernelChart.moduleRep B)
    (RepeatedOddMarkerKernelChart.originalKernelChart B) K (stable B K hK)

/-- Exact classification by actual cocycles on the correlated quotient
V/K. No binary-source or nontrivial-sign hypothesis is needed yet. -/
def fibreCocycleEquiv :
    FixedKernelSubgroupFibre (pullbackProjection B) (kernelGroup B K) ≃
      cocycles₁ (TernaryDiagonalQuotientCocycles.quotientRep
        (RepeatedOddMarkerKernelChart.signCharacter B) K hK) := by
  letI : (kernelGroup B K).Normal := kernelGroup_normal B K hK
  let π := QuotientGroup.lift (kernelGroup B K) (pullbackProjection B) (kernelGroup_le B K)
  let A := OriginalKernelQuotientChart.quotientModule
    (RepeatedOddMarkerKernelChart.moduleRep B) K (stable B K hK)
  let E : OriginalKernelModuleChart π A :=
    OriginalKernelQuotientChart.quotientChart (pullbackProjection B)
      (RepeatedOddMarkerKernelChart.moduleRep B)
      (RepeatedOddMarkerKernelChart.originalKernelChart B) K (stable B K hK)
      (kernelGroup B K) (kernelGroup_le B K)
      (OriginalKernelQuotientChart.chart_mem_submoduleGroup (pullbackProjection B)
        (RepeatedOddMarkerKernelChart.moduleRep B)
        (RepeatedOddMarkerKernelChart.originalKernelChart B) K)
  exact (fixedKernelLiftEquiv (pullbackProjection B) (kernelGroup B K) (kernelGroup_le B K)).trans
    (homomorphicLiftModuleCocycleEquiv π (MonoidHom.id B) A E
      (quotientSectionLift B (kernelGroup B K) (kernelGroup_le B K)))

include hK in
/-- Exact fibre cardinality, with the actual binary source and every
original coordinate's nontrivial sign explicitly required. -/
theorem card_fibre (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    Nat.card (FixedKernelSubgroupFibre (pullbackProjection B) (kernelGroup B K)) =
      Nat.card ((ι → ZMod 3) ⧸ K) := by
  rw [Nat.card_congr (fibreCocycleEquiv B K hK)]
  exact TernaryDiagonalQuotientCocycles.cocycles_card
    (RepeatedOddMarkerKernelChart.signCharacter B) K hK hB hχ

include hK in
theorem card_fibre_pow (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    Nat.card (FixedKernelSubgroupFibre (pullbackProjection B) (kernelGroup B K)) =
      3 ^ (Fintype.card ι - Module.finrank (ZMod 3) K) := by
  rw [Nat.card_congr (fibreCocycleEquiv B K hK)]
  exact TernaryDiagonalQuotientCocycles.cocycles_card_pow
    (RepeatedOddMarkerKernelChart.signCharacter B) K hK hB hχ

/-- The same kernel as an actual subgroup of the whole original marker
and exterior product, with no ambient normality assertion. -/
def ambientKernel : Subgroup ((ι → OddMarkerGroup) × D) :=
  (kernelGroup B K).map (pullback B).subtype

theorem ambientKernel_le : ambientKernel B K ≤ contraction.ker := by
  rintro _ ⟨q, hq, rfl⟩
  have hp := kernelGroup_le B K hq
  exact congrArg Subtype.val hp

theorem ambientKernel_subgroupOf :
    (ambientKernel B K).subgroupOf (pullback B) = kernelGroup B K :=
  Subgroup.comap_map_eq_self_of_injective (pullback B).subtype_injective (kernelGroup B K)

/-- Exact passage between original ambient subgroups and subgroups of
the literal pullback, keeping the same image and kernel throughout. -/
def ambientFibreEquiv :
    FixedImageKernelSubgroupFibre contraction B (ambientKernel B K) ≃
      FixedKernelSubgroupFibre (pullbackProjection B) (kernelGroup B K) := by
  have e := fixedImageKernelSubgroupEquiv contraction B (ambientKernel B K) (ambientKernel_le B K)
  change FixedImageKernelSubgroupFibre contraction B (ambientKernel B K) ≃
    FixedKernelSubgroupFibre (pullbackProjection B)
      ((ambientKernel B K).subgroupOf (pullback B)) at e
  rw [ambientKernel_subgroupOf] at e
  exact e

include hK in
/-- The count is for literal original ambient subgroups with fixed
actual image and kernel, not for abstract groups or labelled parameters. -/
theorem card_ambientFibre (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    Nat.card (FixedImageKernelSubgroupFibre contraction B (ambientKernel B K)) =
      Nat.card ((ι → ZMod 3) ⧸ K) := by
  rw [Nat.card_congr (ambientFibreEquiv B K)]
  exact card_fibre B K hK hB hχ

include hK in
theorem card_ambientFibre_pow (hB : IsPGroup 2 B)
    (hχ : ∀ i, RepeatedOddMarkerKernelChart.signCharacter B i ≠ 1) :
    Nat.card (FixedImageKernelSubgroupFibre contraction B (ambientKernel B K)) =
      3 ^ (Fintype.card ι - Module.finrank (ZMod 3) K) := by
  rw [Nat.card_congr (ambientFibreEquiv B K)]
  exact card_fibre_pow B K hK hB hχ

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerFibreCount

end
