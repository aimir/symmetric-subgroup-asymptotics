import SymmetricSubgroupAsymptotics.E6BraidSystemDerivedStructure
import SymmetricSubgroupAsymptotics.E6BraidSystemDerivedNormalizerIndex
import SymmetricSubgroupAsymptotics.TernaryHeisenbergNormalizerActionBound

/-! Every nontrivial finite action of the derived image of a generated E6
system has at least27 points. Only this actual six-reflection source is
required to be generated. Neither the source nor its derived subgroup is
assumed simple, and the action is not assumed faithful. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.E6BraidSystemDerivedOrbitGap
open InvolutionBraidPresentation E6BraidSystemDerivedWords
open E6BraidSystemDerivedHeisenberg
open CFSGYE6SelectedWords (adjacent)
variable {G : Type*} [Group G] (S : System adjacent G)

/-- Paired inversion detects the selected root in EVERY homomorphic
image, rather than only in the original abstract source. -/
theorem map_diagonal_ne_one {K : Type*} [Group K]
    (f : commutator G →* K) (ha : f (a S)≠1) :
    f (E6BraidSystemDerivedNormalizerIndex.z S)≠1 := by
  have h : TernaryThreeCycleHeisenberg.diagonal (f (a S)) (f (b S)) (f (c S))≠1 := by
    apply TernaryThreeCycleHeisenberg.diagonal_ne_one _ _ _
      (MulAut.conj (f (firstInverter S))).toMonoidHom
      (MulAut.conj (f (secondInverter S))).toMonoidHom
    · rw [←map_pow,a_cube,map_one]
    · rw [←map_pow,b_cube,map_one]
    · rw [←map_pow,c_cube,map_one]
    · exact (a_commutes_b S).map f
    · exact (a_commutes_c S).map f
    · exact (b_commutes_c S).map f
    · change f (firstInverter S)*f (a S)*(f (firstInverter S))⁻¹=(f (a S))⁻¹
      simpa only [map_mul,map_inv] using congrArg f (first_a S)
    · change f (firstInverter S)*f (b S)*(f (firstInverter S))⁻¹=(f (b S))⁻¹
      simpa only [map_mul,map_inv] using congrArg f (first_b S)
    · change f (firstInverter S)*f (c S)*(f (firstInverter S))⁻¹=f (c S)
      simpa only [map_mul,map_inv] using congrArg f (first_c S)
    · change f (secondInverter S)*f (a S)*(f (secondInverter S))⁻¹=(f (a S))⁻¹
      simpa only [map_mul,map_inv] using congrArg f (second_a S)
    · change f (secondInverter S)*f (b S)*(f (secondInverter S))⁻¹=f (b S)
      simpa only [map_mul,map_inv] using congrArg f (second_b S)
    · change f (secondInverter S)*f (c S)*(f (secondInverter S))⁻¹=(f (c S))⁻¹
      simpa only [map_mul,map_inv] using congrArg f (second_c S)
    · exact ha
  simpa only [E6BraidSystemDerivedNormalizerIndex.z,
    TernaryThreeCycleHeisenberg.diagonal,map_mul,map_inv] using h

/-- A nontrivial action of the ACTUAL derived six-reflection source has
at least27 points. This is designed to be applied to each actual orbit
and to actual commuting-cycle quotients. -/
theorem card_ge_twentySeven_of_nontrivial_action
    (hgen : Subgroup.closure (Set.range S.generator)=⊤)
    [Finite (commutator G)] {X : Type*} [Finite X]
    [MulAction (commutator G) X]
    (hmove : ∃ g : commutator G, ∃ x : X, g • x≠x) : 27≤Nat.card X := by
  let ρ : commutator G →* Equiv.Perm X := MulAction.toPermHom _ _
  have ha : ρ (a S)≠1 := by
    intro hh
    have he : ρ=1 := E6BraidSystemDerivedStructure.anchor_hom_trivial S hgen ρ hh
    rcases hmove with ⟨g,x,hx⟩
    have hfix := congrArg (fun p : Equiv.Perm X => p x) (DFunLike.congr_fun he g)
    exact hx hfix
  have hz := map_diagonal_ne_one S ρ ha
  have hex : ∃ x : X, E6BraidSystemDerivedNormalizerIndex.z S • x≠x := by
    by_contra hh
    push_neg at hh
    apply hz
    ext x
    exact hh x
  obtain ⟨x,hx⟩ := hex
  let f := E6BraidSystemDerivedHeisenberg.hom S
  have hu : ∀ h, q S*f h*(q S)⁻¹=
      f (QuaternaryPauliFourierPhaseNormalization.rotation h) := by
    apply TernaryHeisenbergGeneratorNormalizer.rotation_normalizes
    · simpa only [f,E6BraidSystemDerivedNormalizerIndex.hom_first,
        E6BraidSystemDerivedNormalizerIndex.hom_second] using fourier_first S
    · simpa only [f,E6BraidSystemDerivedNormalizerIndex.hom_first,
        E6BraidSystemDerivedNormalizerIndex.hom_second] using fourier_second S
    · simpa only [f,E6BraidSystemDerivedNormalizerIndex.hom_third] using
        E6BraidSystemDerivedNormalizerIndex.fourier_third S
  have hv : ∀ h, E6BraidSystemDerivedNormalizerIndex.lower S*f h*
      (E6BraidSystemDerivedNormalizerIndex.lower S)⁻¹=
        f (QuaternaryPauliFourierPhaseNormalization.shear h) := by
    apply TernaryHeisenbergGeneratorNormalizer.shear_normalizes
    · simpa only [f,E6BraidSystemDerivedNormalizerIndex.hom_first,
        E6BraidSystemDerivedNormalizerIndex.hom_second] using
        E6BraidSystemDerivedNormalizerIndex.lower_first S
    · simpa only [f,E6BraidSystemDerivedNormalizerIndex.hom_second] using
        E6BraidSystemDerivedNormalizerIndex.lower_second S
    · simpa only [f,E6BraidSystemDerivedNormalizerIndex.hom_third] using
        E6BraidSystemDerivedNormalizerIndex.lower_third S
  apply TernaryHeisenbergNormalizerActionBound.card_ge_twentySeven_of_central_moved
    f (q S) (E6BraidSystemDerivedNormalizerIndex.lower S)
    QuaternaryPauliFourierPhaseNormalization.rotation
    QuaternaryPauliFourierPhaseNormalization.shear hu hv
    QuaternaryPauliFourierPhaseNormalization.rotation_coordinates
    QuaternaryPauliFourierPhaseNormalization.shear_coordinates x
  simpa only [f,E6BraidSystemDerivedNormalizerIndex.hom_third] using hx

end SymmetricSubgroupAsymptotics.E6BraidSystemDerivedOrbitGap
