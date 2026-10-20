import SymmetricSubgroupAsymptotics.ModuleFiniteCoordinateGenerators
import SymmetricSubgroupAsymptotics.RepresentationCoordinateHeads

/-! Actual representation generators from the original joint coordinate
filtration. Only literal coordinate subrepresentations are bounded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra BigOperators
namespace SymmetricSubgroupAsymptotics

/-- There is no decomposition or splitting assumption on the source
representation. Its actual kernels supply the required finite filtration. -/
theorem representationGeneratedBy_of_finite_coordinate_bounds
    {k G V I : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Fintype I]
    (W : I → Type) [∀ i,AddCommGroup (W i)] [∀ i,Module k (W i)]
    (rho : Representation k G V) (tau : ∀ i,Representation k G (W i)) (b : I → ℕ)
    (hb : ∀ i (S : Subrepresentation (tau i)),RepresentationGeneratedBy S.toRepresentation (b i))
    (f : ∀ i,rho.IntertwiningMap (tau i))
    (hf : Function.Injective (fun v i => f i v)) :
    RepresentationGeneratedBy rho (∑ i,b i) := by
  let fi : ∀ i,rho.asModule →ₗ[k[G]] (tau i).asModule := fun i =>
    Representation.IntertwiningMap.equivLinearMapAsModule rho (tau i) (f i)
  have hi : Function.Injective (fun v i => fi i v) := hf
  have hlocal : ∀ i (S : Submodule k[G] (tau i).asModule),
      ModuleGeneratedBy k[G] S (b i) := by
    intro i S
    have h := hb i (Subrepresentation.ofSubmodule' S)
    exact ModuleGeneratedBy.congr (submoduleRepresentationModuleEquiv (tau i) S).symm h
  exact ModuleGeneratedBy.of_finite_coordinate_bounds
    (fun i => (tau i).asModule) b hlocal fi hi

end SymmetricSubgroupAsymptotics
