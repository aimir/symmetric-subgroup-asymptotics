import SymmetricSubgroupAsymptotics.ModuleGeneratorExactSequence
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! Uniform module-generator bounds add across two actual jointly
injective intertwining coordinates. Kernel/image lifting takes place in
the same original representation and the same group algebra. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.RepresentationUniformJointCoordinates

variable {k G V W Z : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup Z] [Module k Z]
    {rho : Representation k G V} {sigma : Representation k G W}
    {tau : Representation k G Z}

/-- Actual module generators lift from the literal kernel and image of
an original intertwining map. -/
theorem generatedBy_of_kernel_range (f : rho.IntertwiningMap sigma)
    {m n : ℕ} (hker : RepresentationGeneratedBy f.ker.toRepresentation m)
    (hrange : RepresentationGeneratedBy f.range.toRepresentation n) :
    RepresentationGeneratedBy rho (m+n) := by
  let inc := RepresentationHeadExact.kernelInclusion f
  let q := RepresentationHeadExact.rangeProjection f
  let I : f.ker.toRepresentation.asModule →ₗ[k[G]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ inc
  let Q : rho.asModule →ₗ[k[G]] f.range.toRepresentation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ q
  have hexact : LinearMap.range I = LinearMap.ker Q := by
    ext v
    change (rho.asModuleEquiv v ∈ inc.toLinearMap.range) ↔
      (rho.asModuleEquiv v ∈ q.toLinearMap.ker)
    exact Iff.of_eq (congrArg (fun S : Submodule k V => rho.asModuleEquiv v ∈ S)
      (RepresentationHeadExact.kernelInclusion_range f))
  have hq : Function.Surjective Q := RepresentationHeadExact.rangeProjection_surjective f
  obtain ⟨u,hu⟩ := hker
  obtain ⟨w,hw⟩ := hrange
  exact ModuleGeneratorExactSequence.span_tuple_of_exact I Q hexact hq u hu w hw

variable [Finite k] [Finite V] [Finite W] [Finite Z]

/-- Two actual uniform coordinate bounds add. Joint injectivity is proved
for the original maps, rather than replaced by a product decomposition. -/
theorem uniform_of_jointly_injective
    (f : rho.IntertwiningMap sigma) (g : rho.IntertwiningMap tau)
    (hjoint : ∀ v w : V, f v = f w → g v = g w → v = w)
    {n m : ℕ} (hsigma : UniformSubrepresentationGeneratorBound sigma n)
    (htau : UniformSubrepresentationGeneratorBound tau m) :
    UniformSubrepresentationGeneratorBound rho (n+m) := by
  intro M
  let inclusion : M.toRepresentation.IntertwiningMap rho := {
    toLinearMap := M.toSubmodule.subtype
    isIntertwining' _ := rfl }
  let fM := f.comp inclusion
  let gM := g.comp inclusion
  let j : fM.ker.toRepresentation.IntertwiningMap tau :=
    gM.comp (RepresentationHeadExact.kernelInclusion fM)
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply hjoint
    · exact x.property.trans y.property.symm
    · exact h
  have hK : RepresentationGeneratedBy fM.ker.toRepresentation m :=
    representationGeneratedBy_of_injective_of_uniform htau j hj
  have hR : RepresentationGeneratedBy fM.range.toRepresentation n := hsigma fM.range
  simpa only [Nat.add_comm] using generatedBy_of_kernel_range fM hK hR

end SymmetricSubgroupAsymptotics.RepresentationUniformJointCoordinates
