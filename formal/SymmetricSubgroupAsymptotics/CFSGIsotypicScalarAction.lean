import SymmetricSubgroupAsymptotics.CFSGIsotypicCommutativeScalarField
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! The scalar-image quotient acts faithfully on the original carrier.
This is the actual quotient of the acting group algebra, rather than an
unrelated finite field supplied with a semilinear representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.CFSGIsotypicScalarAction
open CFSGIsotypicCommutativeScalarField

variable {k A V : Type} [Field k] [CommGroup A]
  [AddCommGroup V] [Module k V] (rho : Representation k A V)

def scalarAction : scalarQuotient rho →ₐ[k] Module.End k V :=
  Ideal.kerLiftAlg rho.asAlgebraHom

theorem scalarAction_injective : Function.Injective (scalarAction rho) :=
  Ideal.kerLiftAlg_injective rho.asAlgebraHom

theorem scalarAction_mk (r : k[A]) :
    scalarAction rho (Ideal.Quotient.mk (RingHom.ker rho.asAlgebraHom.toRingHom) r) =
      rho.asAlgebraHom r := rfl

@[reducible] def scalarModule : Module (scalarQuotient rho) V :=
  Module.compHom V (scalarAction rho).toRingHom

attribute [local instance] scalarModule

theorem scalar_smul_apply (a : scalarQuotient rho) (v : V) :
    a • v = scalarAction rho a v := rfl

@[reducible] def scalarTower : IsScalarTower k (scalarQuotient rho) V :=
  IsScalarTower.of_algebraMap_smul (fun a v => by
    change scalarAction rho (algebraMap k (scalarQuotient rho) a) v = a • v
    rw [(scalarAction rho).commutes]
    rfl)

attribute [local instance] scalarTower

theorem scalar_mk_single (a : A) (v : V) :
    (Ideal.Quotient.mk (RingHom.ker rho.asAlgebraHom.toRingHom)
      (MonoidAlgebra.single a (1 : k))) • v = rho a v := by
  rw [scalar_smul_apply, scalarAction_mk, Representation.asAlgebraHom_single_one]

@[reducible] def scalarFaithful : FaithfulSMul (scalarQuotient rho) V where
  eq_of_smul_eq_smul h := by
    apply scalarAction_injective rho
    apply LinearMap.ext
    exact h

theorem scalarQuotient_finite [Finite V] : Finite (scalarQuotient rho) := by
  letI : Finite (Module.End k V) := Finite.of_injective
    (fun f : Module.End k V => (f : V → V)) DFunLike.coe_injective
  exact Finite.of_injective (scalarAction rho) (scalarAction_injective rho)

section Field
variable [Finite V] [Nontrivial V]

local instance : Finite rho.asModule :=
  Finite.of_injective rho.asModuleEquiv rho.asModuleEquiv.injective
local instance : Module.Finite k[A] rho.asModule := Module.Finite.of_finite
local instance : Nontrivial rho.asModule := rho.asModuleEquiv.toEquiv.nontrivial

variable (hss : IsSemisimpleModule k[A] rho.asModule) (hiso : IsIsotypic k[A] rho.asModule)

include hss hiso in
theorem scalar_dimension_product :
    Module.finrank k (scalarQuotient rho) * Module.finrank (scalarQuotient rho) V =
      Module.finrank k V := by
  letI : IsSemisimpleModule k[A] rho.asModule := hss
  letI : Field (scalarQuotient rho) := scalarField rho hiso
  letI : StrongRankCondition (scalarQuotient rho) := commRing_strongRankCondition _
  letI : Finite (scalarQuotient rho) := scalarQuotient_finite rho
  letI : Module.Finite k (scalarQuotient rho) := Module.Finite.of_finite
  letI : Module.Finite (scalarQuotient rho) V := Module.Finite.of_finite
  exact Module.finrank_mul_finrank k (scalarQuotient rho) V

end Field

end SymmetricSubgroupAsymptotics.CFSGIsotypicScalarAction
