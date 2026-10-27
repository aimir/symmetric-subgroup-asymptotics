import SymmetricSubgroupAsymptotics.E6BraidSystemDerivedHeisenberg
import SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorNormalizer

/-! Selected actual Fourier/shear words in the ACTUAL ambient commutator
supply index27. Only that derived group must be finite/simple; the ambient
six-involution group need not be. The nontrivial selected cube is an
explicit literal hypothesis for internal installation, not a T1 callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.E6BraidSystemDerivedNormalizerIndex
open InvolutionBraidPresentation E6BraidSystemDerivedWords
open CFSGYE6SelectedWords (adjacent)
variable {G : Type*} [Group G] (S : System adjacent G)

abbrev x : commutator G := TernaryThreeCycleHeisenberg.difference (a S) (b S)
abbrev z : commutator G := TernaryThreeCycleHeisenberg.diagonal (a S) (b S) (c S)
def lower : commutator G := TernaryHeisenbergGeneratorNormalizer.lowerWord (q S) (a S)

 theorem fourier_third : q S*z S*(q S)⁻¹=z S :=
  TernaryHeisenbergGeneratorNormalizer.central_fixed_of_fourier (x S) (r S) (z S) (q S)
    (TernaryThreeCycleHeisenberg.difference_commute_diagonal _ _ _
      (a_commutes_b S) (a_commutes_c S) (b_commutes_c S))
    (TernaryThreeCycleHeisenberg.collecting_relation _ _ _ _ (b_cube S)
      (a_commutes_b S) (a_commutes_c S) (rotation_a S) (rotation_b S) (rotation_c S))
    (fourier_first S) (fourier_second S)

 theorem root_first : a S*x S*(a S)⁻¹=x S :=
  TernaryThreeCycleHeisenberg.root_conjugates_difference _ _ (a_commutes_b S)
 theorem root_second : a S*r S*(a S)⁻¹=x S*r S :=
  TernaryThreeCycleHeisenberg.root_conjugates_rotation _ _ _ (rotation_a S)
 theorem root_third : a S*z S*(a S)⁻¹=z S :=
  TernaryThreeCycleHeisenberg.root_conjugates_diagonal _ _ _ (a_commutes_b S) (a_commutes_c S)

 theorem lower_first : lower S*x S*(lower S)⁻¹=x S*r S :=
  TernaryHeisenbergGeneratorNormalizer.lower_first _ _ _ _
    (root_first S) (root_second S) (fourier_first S) (fourier_second S)
 theorem lower_second : lower S*r S*(lower S)⁻¹=r S :=
  TernaryHeisenbergGeneratorNormalizer.lower_second _ _ _ _ (root_first S) (fourier_first S)
 theorem lower_third : lower S*z S*(lower S)⁻¹=z S :=
  TernaryHeisenbergGeneratorNormalizer.lower_third _ _ _ (root_third S) (fourier_third S)

 theorem hom_first : E6BraidSystemDerivedHeisenberg.hom S TernaryHeisenbergGeneratorExt.first=x S := by
  unfold E6BraidSystemDerivedHeisenberg.hom TernaryThreeCycleHeisenberg.hom
  exact TernaryHeisenbergGeneratorExt.hom_first _ _ _ _ _ _ _ _ _
 theorem hom_second : E6BraidSystemDerivedHeisenberg.hom S TernaryHeisenbergGeneratorExt.second=r S := by
  unfold E6BraidSystemDerivedHeisenberg.hom TernaryThreeCycleHeisenberg.hom
  exact TernaryHeisenbergGeneratorExt.hom_second _ _ _ _ _ _ _ _ _
 theorem hom_third : E6BraidSystemDerivedHeisenberg.hom S TernaryHeisenbergGeneratorExt.third=z S := by
  unfold E6BraidSystemDerivedHeisenberg.hom TernaryThreeCycleHeisenberg.hom
  exact TernaryHeisenbergGeneratorExt.hom_third _ _ _ _ _ _ _ _ _

 theorem proper_index_ge_twentySeven [Finite (commutator G)] [IsSimpleGroup (commutator G)]
    (ha : a S≠1) (H : Subgroup (commutator G)) (hH : H≠⊤) : 27≤H.index := by
  apply TernaryHeisenbergGeneratorNormalizer.proper_index_ge_twentySeven
    (E6BraidSystemDerivedHeisenberg.hom S) (E6BraidSystemDerivedHeisenberg.hom_injective S ha)
    (q S) (lower S)
  · simpa only [hom_first,hom_second] using fourier_first S
  · simpa only [hom_first,hom_second] using fourier_second S
  · simpa only [hom_third] using fourier_third S
  · simpa only [hom_first,hom_second] using lower_first S
  · simpa only [hom_second] using lower_second S
  · simpa only [hom_third] using lower_third S
  · exact hH

end SymmetricSubgroupAsymptotics.E6BraidSystemDerivedNormalizerIndex
