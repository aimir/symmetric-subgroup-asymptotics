import SymmetricSubgroupAsymptotics.WreathNormalBaseCoordinates
import SymmetricSubgroupAsymptotics.CliffordRawRestrictionInput
import SymmetricSubgroupAsymptotics.RepresentationSemisimpleSurjectiveInflation
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation

/-! Raw local Clifford semisimplicity gives semisimplicity of the whole
coordinate module on the literal block kernel. Evaluation embeds it in
the finite product of the actual inflated local restrictions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open PermutationalWreathProduct WreathNormalBaseCoordinates

 theorem wreath_kernel_restriction_semisimple
    (raw : CliffordRawRestriction.Input)
    {k G D Q I V : Type} [Field k] [Group G] [Group D] [Finite D]
    [Group Q] [Fintype I] [MulAction Q I]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : G →* PermutationalWreathProduct D Q I)
    (hfull : Compression.FullComponent rho)
    (beta : Representation k D V) (hirr : Representation.IsIrreducible beta) :
    let K := (rightHom.comp rho).ker
    let restriction : Representation k K (I → V) :=
      ((functionRepresentation beta).comp rho).comp K.subtype
    IsSemisimpleModule k[K] restriction.asModule := by
  let K := (rightHom.comp rho).ker
  let tau : Representation k K (I → V) := ((functionRepresentation beta).comp rho).comp K.subtype
  let f (i : I) : K →* D := coordinate rho K le_rfl i
  let sigma (i : I) : Representation k K V := beta.comp (f i)
  have hsemi (i : I) : IsSemisimpleModule k[K] (sigma i).asModule := by
    let Li := (f i).range
    letI : Li.Normal := coordinate_range_normal rho K le_rfl hfull i
    let restricted : Representation k Li V := beta.comp Li.subtype
    letI : IsSemisimpleModule k[Li] restricted.asModule := raw.semisimple beta hirr Li
    exact representation_isSemisimpleModule_comp (f i).rangeRestrict
      (f i).rangeRestrict_surjective (beta.comp Li.subtype)
  letI (i : I) : IsSemisimpleModule k[K] (sigma i).asModule := hsemi i
  let ev (i : I) : tau.IntertwiningMap (sigma i) :=
    { toLinearMap := LinearMap.proj i
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        change beta ((rho g.val).left i) (v ((rho g.val).right⁻¹ • i))=
          beta ((rho g.val).left i) (v i)
        rw [show (rho g.val).right=1 from g.property,inv_one,one_smul] }
  let fm (i : I) : tau.asModule →ₗ[k[K]] (sigma i).asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ (ev i)
  let all : tau.asModule →ₗ[k[K]] (∀ i : I,(sigma i).asModule) := LinearMap.pi fm
  have hinj : Function.Injective all := by
    intro v w h
    apply tau.asModuleEquiv.injective
    funext i
    exact congrArg (fun a => (sigma i).asModuleEquiv (a i)) h
  exact IsSemisimpleModule.of_injective all hinj

end SymmetricSubgroupAsymptotics
