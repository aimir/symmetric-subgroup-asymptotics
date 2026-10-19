import SymmetricSubgroupAsymptotics.SemisimpleNormalKernelSubquotientFaithfulness
import SymmetricSubgroupAsymptotics.WreathNormalKernelFixedFreeEnvelope
import SymmetricSubgroupAsymptotics.WreathKernelSemisimpleRestriction

/-! The actual-wreath faithfulness corollary of raw modular Clifford.
All fixed-space and semisimple-envelope facts are proved from literal
coordinates. Only a displayed injected submodule and its actual quotient
map remain as structural arguments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open PermutationalWreathProduct

 theorem wreath_kernel_subquotient_faithful
    (raw : CliffordRawRestriction.Input)
    {k G D Q I V A W : Type} [Field k] [Group G] [Group D] [Finite D]
    [Group Q] [Fintype I] [MulAction Q I] [MulAction.IsPretransitive Q I]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup A] [Module k A]
    [AddCommGroup W] [Module k W] [Nontrivial W]
    (rho : G →* PermutationalWreathProduct D Q I)
    (hrho : Function.Injective rho)
    (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho)
    (beta : Representation k D V) (hirr : Representation.IsIrreducible beta)
    (hfaithful : Function.Injective beta)
    (sigma : Representation k G A) (tau : Representation k G W)
    (j : sigma.IntertwiningMap ((functionRepresentation beta).comp rho))
    (hj : Function.Injective j)
    (q : sigma.IntertwiningMap tau) (hq : Function.Surjective q) :
    Function.Injective (tau.comp (rightHom.comp rho).ker.subtype) := by
  let K := (rightHom.comp rho).ker
  let full : Representation k G (I → V) := (functionRepresentation beta).comp rho
  letI : IsSemisimpleModule k[K] (Representation.asModule (full.comp K.subtype)) :=
    wreath_kernel_restriction_semisimple raw rho hfull beta hirr
  letI : Representation.IsIrreducible beta := hirr
  apply faithful_normal_restriction_of_semisimple_subquotient K full sigma tau j hj q hq
  intro L _ hL hne v hv
  exact wreath_normal_kernel_fixed_free rho hrho htop hfull beta hfaithful L hL hne v hv

end SymmetricSubgroupAsymptotics
