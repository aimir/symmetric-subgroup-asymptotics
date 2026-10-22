import SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarConjugation
import Mathlib.Algebra.Ring.Aut

/-! The ambient group acts by actual ring automorphisms on the scalar
quotient of its abelian normal subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarAutomorphisms
open CFSGIsotypicCommutativeScalarField CFSGNormalAbelianScalarConjugation

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal] [IsMulCommutative H]

theorem scalarConjugationHom_one :
    scalarConjugationHom rho H 1 = RingHom.id (scalarQuotient (restriction rho H)) := by
  apply RingHom.ext
  rintro ⟨r⟩
  change Ideal.Quotient.mk _ (algebraConjugation (k := k) H 1 r) =
    Ideal.Quotient.mk _ r
  exact congrArg (Ideal.Quotient.mk _)
    (congrArg (fun f : k[H] →ₐ[k] k[H] => f r) (algebraConjugation_one (k := k) H))

theorem scalarConjugationHom_mul (g h : G) :
    scalarConjugationHom rho H (g * h) =
      (scalarConjugationHom rho H g).comp (scalarConjugationHom rho H h) := by
  apply RingHom.ext
  rintro ⟨r⟩
  change Ideal.Quotient.mk _ (algebraConjugation (k := k) H (g * h) r) =
    Ideal.Quotient.mk _
      (algebraConjugation (k := k) H g (algebraConjugation (k := k) H h r))
  exact congrArg (Ideal.Quotient.mk _)
    (congrArg (fun f : k[H] →ₐ[k] k[H] => f r) (algebraConjugation_mul (k := k) H g h))

def scalarConjugation (g : G) :
    scalarQuotient (restriction rho H) ≃+* scalarQuotient (restriction rho H) where
  __ := scalarConjugationHom rho H g
  invFun := scalarConjugationHom rho H g⁻¹
  left_inv a := by
    calc
      scalarConjugationHom rho H g⁻¹ (scalarConjugationHom rho H g a) =
          scalarConjugationHom rho H (g⁻¹ * g) a :=
        (congrArg (fun f => f a) (scalarConjugationHom_mul rho H g⁻¹ g)).symm
      _ = a := by rw [inv_mul_cancel, scalarConjugationHom_one]; rfl
  right_inv a := by
    calc
      scalarConjugationHom rho H g (scalarConjugationHom rho H g⁻¹ a) =
          scalarConjugationHom rho H (g * g⁻¹) a :=
        (congrArg (fun f => f a) (scalarConjugationHom_mul rho H g g⁻¹)).symm
      _ = a := by rw [mul_inv_cancel, scalarConjugationHom_one]; rfl

def scalarAutomorphismHom : G →*
    (scalarQuotient (restriction rho H) ≃+* scalarQuotient (restriction rho H)) where
  toFun := scalarConjugation rho H
  map_one' := by
    apply RingEquiv.ext
    intro a
    exact congrArg (fun f => f a) (scalarConjugationHom_one rho H)
  map_mul' g h := by
    apply RingEquiv.ext
    intro a
    exact congrArg (fun f => f a) (scalarConjugationHom_mul rho H g h)

end SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarAutomorphisms
