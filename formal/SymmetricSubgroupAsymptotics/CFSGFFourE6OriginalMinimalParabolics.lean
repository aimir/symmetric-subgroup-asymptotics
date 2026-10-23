import SymmetricSubgroupAsymptotics.CFSGFFourE6GeneratedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection
import SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups

/-! The original simple F4 Sylow normalizer has exactly four minimal
strict overgroups, the images of the literal relative simple parabolics.
The actual central kernel and positive Sylow injection justify all
normalizer reflection and subgroup correspondences. No original
automorphism is lifted to a matrix source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMinimalParabolics
open CFSGFFourSerreMatrices CFSGFFourE6GeneratedOriginalProjection
open CFSGFFourE6OriginalProjection CFSGFFourE6OriginalCentralKernel
open CFSGFFourE6OriginalOppositeAlignment CFSGFFourE6PositiveSylow
open CFSGE6GeckGeneratedParabolics CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGSurjectiveMinimalOvergroups
open CFSGCentralKernelPSubgroupReflection CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

def originalSimpleParabolic (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    Subgroup (Projective CartanMatrix.F₄ K) :=
  (parabolicGenerated K (RingEquiv.refl K) a).map (generatedToOriginal K)

theorem upperGenerated_map_original (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (upperGenerated K (RingEquiv.refl K)).map (generatedToOriginal K) =
      Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)) := by
  let P : Subgroup (canonicalElementaryGroup realizationData K) := positiveSylow K p
  have hB : (upperGenerated K (RingEquiv.refl K)).map (foldedEquiv K).toMonoidHom =
      Subgroup.normalizer (P : Set (canonicalElementaryGroup realizationData K)) := by
    rw [upperGenerated_eq_normalizer, Subgroup.map_equiv_normalizer_eq,
      rootPart_positive_folded_image K p]
  have href (g : canonicalElementaryGroup realizationData K) :
      foldedToOriginal K g ∈ Subgroup.normalizer (P.map (foldedToOriginal K) :
        Set (Projective CartanMatrix.F₄ K)) ↔ g ∈ Subgroup.normalizer
          (P : Set (canonicalElementaryGroup realizationData K)) :=
    mem_normalizer_map_iff (foldedToOriginal K) (positiveSylow K p)
      (foldedPositiveToOriginal_injective K p) (foldedToOriginal_kernel_le_center K p)
      P (positiveSylow K p).isPGroup' g
  have hN : (Subgroup.normalizer (P : Set (canonicalElementaryGroup realizationData K))).map
      (foldedToOriginal K) = Subgroup.normalizer
        (P.map (foldedToOriginal K) : Set (Projective CartanMatrix.F₄ K)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact (href g).mpr hg
    · intro x hx
      obtain ⟨g, rfl⟩ := foldedToOriginal_surjective K x
      exact ⟨g, (href g).mp hx, rfl⟩
  rw [generatedToOriginal, ← Subgroup.map_map, hB, hN]
  exact congrArg (fun S : Subgroup (Projective CartanMatrix.F₄ K) =>
    Subgroup.normalizer (S : Set (Projective CartanMatrix.F₄ K)))
    (positiveSylow_original_image K p)

theorem original_upper_lt_simpleParabolic (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (a : Fin 4) :
    Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)) <
      originalSimpleParabolic K a := by
  have hh := map_lt_map_of_kernel_le (generatedToOriginal K)
    (original_kernel_le_upperGenerated K p)
    (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a)
  rwa [upperGenerated_map_original K p] at hh

theorem original_simpleParabolic_minimal (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (a : Fin 4) (H : Subgroup (Projective CartanMatrix.F₄ K))
    (hBH : Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)) < H)
    (hHP : H ≤ originalSimpleParabolic K a) : H = originalSimpleParabolic K a := by
  have hh := map_minimal_overgroup (generatedToOriginal K) (generatedToOriginal_surjective K)
    (original_kernel_le_upperGenerated K p)
    (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a)
    (parabolicGenerated_minimal K (RingEquiv.refl K) a)
  rw [upperGenerated_map_original K p] at hh
  exact hh H hBH hHP

theorem original_minimal_overgroup_eq_simpleParabolic (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (H : Subgroup (Projective CartanMatrix.F₄ K))
    (hBH : Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)) < H)
    (hmin : ∀ M : Subgroup (Projective CartanMatrix.F₄ K),
      Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)) < M →
        M ≤ H → M = H) : ∃ a : Fin 4, H = originalSimpleParabolic K a := by
  apply minimal_overgroup_family_surjective (generatedToOriginal K)
    (generatedToOriginal_surjective K) (original_kernel_le_upperGenerated K p)
    (parabolicGenerated K (RingEquiv.refl K))
  · intro M hBM hminimal
    obtain ⟨a, ha⟩ := exists_parabolicGenerated_le K (RingEquiv.refl K) M hBM
    exact ⟨a, (hminimal _ (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a) ha).symm⟩
  · rwa [upperGenerated_map_original K p]
  · simpa only [upperGenerated_map_original K p] using hmin

theorem originalSimpleParabolic_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Function.Injective (originalSimpleParabolic K) :=
  map_family_injective (generatedToOriginal K) (original_kernel_le_upperGenerated K p)
    (parabolicGenerated K (RingEquiv.refl K))
    (fun a => (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a).le)
    (parabolicGenerated_injective K (RingEquiv.refl K))

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMinimalParabolics
