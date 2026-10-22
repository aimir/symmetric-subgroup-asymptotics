import SymmetricSubgroupAsymptotics.CFSGIsotypicScalarAction
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Ambient conjugation descends to the actual scalar-image quotient of
an abelian normal restriction. The kernel ideal is preserved because
the group-algebra action is intertwined by the original linear operator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarConjugation
open CFSGIsotypicCommutativeScalarField CFSGIsotypicScalarAction

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal] [IsMulCommutative H]

abbrev restriction : Representation k H V := rho.comp H.subtype

def operatorHom : G →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp rho.asGroupHom

theorem operatorHom_apply (g : G) (v : V) : operatorHom rho g v = rho g v := rfl

theorem operatorHom_symm_apply (g : G) (v : V) :
    (operatorHom rho g).symm v = rho g⁻¹ v := by
  change ((operatorHom rho g)⁻¹) v = rho g⁻¹ v
  rw [← map_inv]
  rfl

def algebraConjugation (g : G) : k[H] ≃ₐ[k] k[H] :=
  MonoidAlgebra.domCongr k k (MulAut.conjNormal g)

theorem algebraConjugation_one :
    (algebraConjugation (k := k) H 1).toAlgHom = AlgHom.id k k[H] := by
  apply MonoidAlgebra.algHom_ext
  intro a
  change MonoidAlgebra.domCongr k k (MulAut.conjNormal (1 : G))
    (MonoidAlgebra.single a 1) = MonoidAlgebra.single a 1
  rw [MonoidAlgebra.domCongr_single]
  simp only [map_one, MulAut.one_apply]

theorem algebraConjugation_mul (g h : G) :
    (algebraConjugation (k := k) H (g * h)).toAlgHom =
      (algebraConjugation (k := k) H g).toAlgHom.comp (algebraConjugation (k := k) H h).toAlgHom := by
  apply MonoidAlgebra.algHom_ext
  intro a
  change MonoidAlgebra.domCongr k k (MulAut.conjNormal (g * h))
    (MonoidAlgebra.single a 1) =
      MonoidAlgebra.domCongr k k (MulAut.conjNormal g)
        (MonoidAlgebra.domCongr k k (MulAut.conjNormal h) (MonoidAlgebra.single a 1))
  rw [MonoidAlgebra.domCongr_single, MonoidAlgebra.domCongr_single,
    MonoidAlgebra.domCongr_single, map_mul]
  rfl

theorem representation_conjugation (g : G) :
    (restriction rho H).asAlgebraHom.comp (algebraConjugation (k := k) H g).toAlgHom =
      ((operatorHom rho g).conjAlgEquiv k).toAlgHom.comp
        (restriction rho H).asAlgebraHom := by
  apply MonoidAlgebra.algHom_ext
  intro a
  apply LinearMap.ext
  intro v
  change (restriction rho H).asAlgebraHom
      (MonoidAlgebra.domCongr k k (MulAut.conjNormal g) (MonoidAlgebra.single a 1)) v =
    operatorHom rho g ((restriction rho H).asAlgebraHom
      (MonoidAlgebra.single a 1) ((operatorHom rho g).symm v))
  rw [MonoidAlgebra.domCongr_single, Representation.asAlgebraHom_single_one,
    Representation.asAlgebraHom_single_one]
  change rho (g * (a : G) * g⁻¹) v =
    operatorHom rho g (rho a ((operatorHom rho g).symm v))
  rw [operatorHom_symm_apply, operatorHom_apply]
  simp only [map_mul, Module.End.mul_apply]

theorem conjugation_preserves_kernel (g : G) (r : k[H])
    (hr : r ∈ RingHom.ker (restriction rho H).asAlgebraHom.toRingHom) :
    algebraConjugation (k := k) H g r ∈
      RingHom.ker (restriction rho H).asAlgebraHom.toRingHom := by
  change (restriction rho H).asAlgebraHom r = 0 at hr
  change (restriction rho H).asAlgebraHom (algebraConjugation (k := k) H g r) = 0
  have he := congrArg (fun f : k[H] →ₐ[k] Module.End k V => f r)
    (representation_conjugation rho H g)
  change (restriction rho H).asAlgebraHom (algebraConjugation (k := k) H g r) =
    (operatorHom rho g).conjAlgEquiv k ((restriction rho H).asAlgebraHom r) at he
  rw [he, hr, map_zero]

def scalarConjugationHom (g : G) :
    scalarQuotient (restriction rho H) →+* scalarQuotient (restriction rho H) :=
  Ideal.quotientMap (RingHom.ker (restriction rho H).asAlgebraHom.toRingHom)
    (algebraConjugation (k := k) H g).toRingEquiv.toRingHom
    (fun r hr => conjugation_preserves_kernel rho H g r hr)

theorem scalarConjugationHom_mk (g : G) (r : k[H]) :
    scalarConjugationHom rho H g
      (Ideal.Quotient.mk (RingHom.ker (restriction rho H).asAlgebraHom.toRingHom) r) =
      Ideal.Quotient.mk (RingHom.ker (restriction rho H).asAlgebraHom.toRingHom)
        (algebraConjugation (k := k) H g r) := rfl

end SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarConjugation
