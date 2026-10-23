import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleRootRanges
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGE6GeckNegativeParabolicRootIntersection
import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! The actual negative native F4 root charts are recovered as
intersections with intrinsic positive minimal parabolics in ORIGINAL F4.
An automorphism preserving the opposed Sylows consequently permutes
this negative family, without a source lift or a length assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalNegativeRootAction
open CFSGFFourE6OriginalSimpleRootRanges CFSGFFourE6OriginalSimpleParameters
open CFSGFFourE6OriginalMinimalParabolics CFSGFFourE6GeneratedOriginalProjection
open CFSGFFourE6OriginalProjection CFSGFFourE6OriginalOppositeAlignment
open CFSGFFourE6OriginalRootIntersection
open CFSGE6GeckNegativeParabolicRootIntersection CFSGE6GeckGeneratedParabolics
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGMinimalOvergroupAutomorphismAction CFSGKernelControlledIntersection CFSG.Models.Chevalley

theorem negativeOrbitRootGenerated_map_original (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    (negativeOrbitRootGenerated K (RingEquiv.refl K) a).map (generatedToOriginal K) =
      (originalSimpleHom K true a).range := by
  rw [negativeOrbitRootGenerated, Subgroup.map_map]
  change (CFSGE6GeckNegativeOrbitRootGroups.fixedOrbitNegative K (RingEquiv.refl K) a).map
    (signedFixedToOriginal K true) = _
  exact negative_orbit_image_eq_simple_range K a

theorem original_negative_inf_simpleParabolic (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (a : Fin 4) : originalNegative K ⊓ originalSimpleParabolic K a =
      (originalSimpleHom K true a).range := by
  have hk : (generatedToOriginal K).ker ≤ parabolicGenerated K (RingEquiv.refl K) a :=
    (original_kernel_le_upperGenerated K p).trans
      (upperGenerated_lt_parabolicGenerated K (RingEquiv.refl K) a).le
  have hh := congrArg (fun S : Subgroup (fixedRootGenerated K (RingEquiv.refl K)) =>
    S.map (generatedToOriginal K))
    (negative_rootPart_inf_parabolicGenerated K (RingEquiv.refl K) (fun _ => rfl) a)
  dsimp only at hh
  rw [map_inf_eq_of_kernel_le_right (generatedToOriginal K) _ _ hk,
    rootPart_negative_original_image, negativeOrbitRootGenerated_map_original] at hh
  exact hh

theorem exists_original_parabolic_permutation (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map f.toMonoidHom =
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K))) :
    ∃ sigma : Equiv.Perm (Fin 4), ∀ a : Fin 4,
      (originalSimpleParabolic K a).map f.toMonoidHom = originalSimpleParabolic K (sigma a) := by
  have hB : (Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K))).map
      f.toMonoidHom = Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)) :=
    (Subgroup.map_equiv_normalizer_eq
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) f).trans
      (congrArg (fun S : Subgroup (Projective CartanMatrix.F₄ K) =>
        Subgroup.normalizer (S : Set (Projective CartanMatrix.F₄ K))) hU)
  exact exists_minimal_overgroup_permutation
    (Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.F₄ K)))
    (originalSimpleParabolic K) (original_upper_lt_simpleParabolic K p)
    (original_simpleParabolic_minimal K p) (original_minimal_overgroup_eq_simpleParabolic K p)
    (originalSimpleParabolic_injective K p) f hB

theorem exists_original_negative_root_permutation (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map f.toMonoidHom =
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)))
    (hV : (originalNegative K).map f.toMonoidHom = originalNegative K) :
    ∃ sigma : Equiv.Perm (Fin 4), ∀ a : Fin 4,
      (originalSimpleHom K true a).range.map f.toMonoidHom =
        (originalSimpleHom K true (sigma a)).range := by
  obtain ⟨sigma, hsigma⟩ := exists_original_parabolic_permutation K p f hU
  refine ⟨sigma, fun a => ?_⟩
  rw [← original_negative_inf_simpleParabolic K p a,
    Subgroup.map_inf _ _ _ f.injective, hV, hsigma a, original_negative_inf_simpleParabolic K p]

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalNegativeRootAction
