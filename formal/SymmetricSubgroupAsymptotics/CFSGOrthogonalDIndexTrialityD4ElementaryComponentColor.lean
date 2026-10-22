import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ComponentColor
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ExtensionParity
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents

/-! Literal elementary D4 transport preserves the genuine component
colour of maximal singular extensions relative to any original
maximal extension. No determinant-only surrogate is used in char2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIndexSingularComponents
open CFSGOrthogonalDIndexTrialityD4ComponentColor
variable (K : Type) [Field K]

theorem elementary_preserves_extension_component_color (g : elementaryRootGroup K 4)
    (B M : MaximalExtensions K) :
    distance 4 B.val (M.val.map (naturalLinearHom K 4 g).toLinearMap) % 2 =
      distance 4 B.val M.val % 2 :=
  component_preserves_all_reference_parities (splitQuadraticForm K 4)
    (splitQuadraticForm_nondegenerate K 4) 4 (naturalSpace_finrank K 4)
    (positiveSpace K 4) B.val M.val (positiveSpace_self_orthogonal K 4)
    (maximalExtension_self_orthogonal K B) (maximalExtension_self_orthogonal K M)
    (positiveSpace_singular K 4)
    (fun x => B.property.2.1 x.val x.property)
    (fun x => M.property.2.1 x.val x.property)
    (naturalLinearHom K 4 g) (elementary_preserves_bundledQ K 0 g)
    (elementary_even_distance K 0 g)

theorem elementary_preserves_extension_component (g : elementaryRootGroup K 4)
    (B M : MaximalExtensions K) :
    Even (distance 4 B.val (M.val.map (naturalLinearHom K 4 g).toLinearMap)) ↔
      Even (distance 4 B.val M.val) := by
  rw [Nat.even_iff, Nat.even_iff, elementary_preserves_extension_component_color]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
