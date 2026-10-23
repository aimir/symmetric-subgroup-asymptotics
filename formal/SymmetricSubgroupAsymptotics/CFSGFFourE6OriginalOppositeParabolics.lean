import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootIntersection
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositionParabolicTransport
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! The four actual opposite parabolics are exactly the minimal strict
overgroups of the negative-Sylow normalizer in ORIGINAL F4. Every
transport is induced by the literal relative opposition word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeParabolics
open CFSGFFourE6OriginalRootIntersection CFSGFFourE6OriginalMinimalParabolics
open CFSGFFourE6GeneratedOriginalProjection CFSGFFourE6OriginalOppositeAlignment
open CFSGFFourE6OriginalProjection CFSGFFourSerreMatrices
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckRelativeOpposition CFSGE6GeckOppositionParabolicTransport
open CFSGE6GeckGeneratedRootIntersection CFSGE6GeckGeneratedParabolics
open CFSGE6GeckMinimalOvergroups CFSGE6GeckOppositeOrbitParabolic
open CFSGSubgroupConjugateRestriction CFSGSurjectiveMinimalOvergroups
open CFSG.Models.Chevalley

def oppositionInGenerated (K : Type) [Field K] : fixedRootGenerated K (RingEquiv.refl K) :=
  ⟨relativeOpposition K, relativeOpposition_mem_generated K (RingEquiv.refl K)⟩

def originalOppositionAut (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : MulAut (Projective CartanMatrix.F₄ K) :=
  MulAut.conj (generatedToOriginal K (oppositionInGenerated K))

theorem rootPart_opposition (K : Type) [Field K] [Finite K] :
    (rootPart K (RingEquiv.refl K) false).map
      (MulAut.conj (oppositionInGenerated K)).toMonoidHom = rootPart K (RingEquiv.refl K) true :=
  restrict_conjugate (fixedRootGenerated K (RingEquiv.refl K)) _ _
    (signedFixed_le_generated K (RingEquiv.refl K) false)
    (signedFixed_le_generated K (RingEquiv.refl K) true)
    (oppositionInGenerated K) (fixed_positive_image_eq_fixed_negative K (RingEquiv.refl K))

theorem original_positive_opposition (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map
      (originalOppositionAut K).toMonoidHom = originalNegative K := by
  have hh := congrArg (fun S : Subgroup (fixedRootGenerated K (RingEquiv.refl K)) =>
    S.map (generatedToOriginal K)) (rootPart_opposition K)
  dsimp only at hh
  rw [map_conjugate, rootPart_positive_original_image K p,
    rootPart_negative_original_image] at hh
  exact hh

theorem original_upper_normalizer_opposition (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K))).map
      (originalOppositionAut K).toMonoidHom =
        Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K)) :=
  (Subgroup.map_equiv_normalizer_eq
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) (originalOppositionAut K)).trans
      (congrArg (fun S : Subgroup (Projective CartanMatrix.F₄ K) =>
        Subgroup.normalizer (S : Set (Projective CartanMatrix.F₄ K))) (original_positive_opposition K p))

theorem original_simpleParabolic_opposition_map (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    (originalSimpleParabolic K a).map (originalOppositionAut K).toMonoidHom =
      originalOppositeParabolic K a := by
  have hh := restrict_conjugate (fixedRootGenerated K (RingEquiv.refl K))
    (simpleParabolic K (fixedRootGenerated K (RingEquiv.refl K)) a)
    (oppositeOrbitParabolic K (RingEquiv.refl K) a)
    (simpleParabolic_le_intermediate K (RingEquiv.refl K) _ le_rfl a)
    (oppositeOrbitParabolic_le_generated K (RingEquiv.refl K) a)
    (oppositionInGenerated K) (simpleParabolic_opposition_map K (RingEquiv.refl K) a)
  have he := congrArg (fun S : Subgroup (fixedRootGenerated K (RingEquiv.refl K)) =>
    S.map (generatedToOriginal K)) hh
  dsimp only at he
  rw [map_conjugate] at he
  exact he

private theorem opposition_kernel_le_upper (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (originalOppositionAut K).toMonoidHom.ker ≤
      Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)) := by
  intro x hx
  have he : x = 1 := (originalOppositionAut K).injective (hx.trans (map_one _).symm)
  rw [he]
  exact Subgroup.one_mem _

theorem original_lower_lt_oppositeParabolic (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K)) <
      originalOppositeParabolic K a := by
  have hh := (Subgroup.map_lt_map_iff_of_injective
    (f := (originalOppositionAut K).toMonoidHom) (originalOppositionAut K).injective).mpr
    (original_upper_lt_simpleParabolic K p a)
  rwa [original_upper_normalizer_opposition K p, original_simpleParabolic_opposition_map] at hh

theorem original_oppositeParabolic_minimal (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (a : Fin 4) (H : Subgroup (Projective CartanMatrix.F₄ K))
    (hBH : Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K)) < H)
    (hHP : H ≤ originalOppositeParabolic K a) : H = originalOppositeParabolic K a := by
  have hh := map_minimal_overgroup (originalOppositionAut K).toMonoidHom
    (originalOppositionAut K).surjective (opposition_kernel_le_upper K p)
    (original_upper_lt_simpleParabolic K p a) (original_simpleParabolic_minimal K p a)
  rw [original_upper_normalizer_opposition K p, original_simpleParabolic_opposition_map] at hh
  exact hh H hBH hHP

theorem original_minimal_overgroup_eq_oppositeParabolic (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (H : Subgroup (Projective CartanMatrix.F₄ K))
    (hBH : Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K)) < H)
    (hmin : ∀ M : Subgroup (Projective CartanMatrix.F₄ K),
      Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.F₄ K)) < M → M ≤ H → M = H) :
    ∃ a : Fin 4, H = originalOppositeParabolic K a := by
  have hh := minimal_overgroup_family_surjective (originalOppositionAut K).toMonoidHom
    (originalOppositionAut K).surjective (opposition_kernel_le_upper K p)
    (originalSimpleParabolic K) (original_minimal_overgroup_eq_simpleParabolic K p) H
  rw [original_upper_normalizer_opposition K p] at hh
  obtain ⟨a, ha⟩ := hh hBH hmin
  exact ⟨a, ha.trans (original_simpleParabolic_opposition_map K a)⟩

theorem originalOppositeParabolic_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Function.Injective (originalOppositeParabolic K) := by
  intro a b he
  apply originalSimpleParabolic_injective K p
  apply Subgroup.map_injective (f := (originalOppositionAut K).toMonoidHom)
    (originalOppositionAut K).injective
  simpa only [original_simpleParabolic_opposition_map] using he

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeParabolics
