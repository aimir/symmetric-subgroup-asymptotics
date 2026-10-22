import SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarAutomorphisms

/-! The literal kernel of the scalar-field automorphism action acts
linearly over the scalar quotient on the original carrier. Faithfulness
is inherited from the original representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarKernel
open CFSGIsotypicCommutativeScalarField CFSGIsotypicScalarAction
  CFSGNormalAbelianScalarConjugation CFSGNormalAbelianScalarAutomorphisms

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal] [IsMulCommutative H]

local instance : Module (scalarQuotient (restriction rho H)) V :=
  scalarModule (restriction rho H)

theorem scalar_intertwining (g : G)
    (a : scalarQuotient (restriction rho H)) (v : V) :
    scalarAction (restriction rho H) (scalarAutomorphismHom rho H g a) (rho g v) =
      rho g (scalarAction (restriction rho H) a v) := by
  refine Quotient.inductionOn' a ?_
  intro r
  change scalarAction (restriction rho H)
    (scalarConjugationHom rho H g (Ideal.Quotient.mk _ r)) (rho g v) =
      rho g (scalarAction (restriction rho H) (Ideal.Quotient.mk _ r) v)
  rw [scalarConjugationHom_mk, scalarAction_mk, scalarAction_mk]
  have he := congrArg (fun f : k[H] →ₐ[k] Module.End k V => f r)
    (representation_conjugation rho H g)
  change (restriction rho H).asAlgebraHom (algebraConjugation (k := k) H g r) =
    (operatorHom rho g).conjAlgEquiv k ((restriction rho H).asAlgebraHom r) at he
  rw [he]
  change operatorHom rho g
      ((restriction rho H).asAlgebraHom r ((operatorHom rho g).symm (rho g v))) = _
  have hv : (operatorHom rho g).symm (rho g v) = v :=
    (operatorHom rho g).symm_apply_apply v
  rw [hv]
  rfl

def kernelLinearMap (g : (scalarAutomorphismHom rho H).ker) :
    Module.End (scalarQuotient (restriction rho H)) V where
  toFun := rho g.val
  map_add' := (rho g.val).map_add
  map_smul' a v := by
    have ha : scalarAutomorphismHom rho H g.val a = a :=
      congrArg (fun f : scalarQuotient (restriction rho H) ≃+*
        scalarQuotient (restriction rho H) => f a) (MonoidHom.mem_ker.mp g.property)
    have he := scalar_intertwining rho H g.val a v
    rw [ha] at he
    exact he.symm

def kernelRepresentation : Representation (scalarQuotient (restriction rho H))
    (scalarAutomorphismHom rho H).ker V where
  toFun := kernelLinearMap rho H
  map_one' := by
    apply LinearMap.ext
    intro v
    change rho 1 v = v
    simp only [map_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change rho (g.val * h.val) v = rho g.val (rho h.val v)
    simp only [map_mul, Module.End.mul_apply]

theorem kernelRepresentation_injective (hf : Function.Injective rho) :
    Function.Injective (kernelRepresentation rho H) := by
  intro g h he
  apply Subtype.ext
  apply hf
  apply LinearMap.ext
  intro v
  exact congrArg (fun f : Module.End (scalarQuotient (restriction rho H)) V => f v) he

end SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarKernel
