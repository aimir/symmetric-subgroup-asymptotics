import SymmetricSubgroupAsymptotics.BinaryQuadraticField
import Mathlib.RepresentationTheory.Basic

/-! Scalar linearity is derived from actual commutation with omega.
Use this only on the actual cubic centralizer subgroup; a larger S4
normalizer can act semilinearly and is not asserted scalar-linear. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCubicScalarLinearRepresentation
open BinaryQuadraticField (Scalar omega)

variable {H V : Type} [Group H] [AddCommGroup V]
  [Module (ZMod 2) V] [Module Scalar V] [IsScalarTower (ZMod 2) Scalar V]
  (rho : Representation (ZMod 2) H V) (k : H)
  (hk : ∀ v, rho k v=omega • v)
  (hcentral : ∀ h : H, Commute h k)

include hk hcentral in
theorem omega_commutes (h : H) (v : V) : rho h (omega • v)=omega • rho h v := by
  rw [← hk,← hk]
  have hh := congrArg (fun g : H => rho g v) (hcentral h).eq
  simpa only [map_mul,Module.End.mul_apply] using hh

/-- Every operator of the actual centralizing subgroup is scalar-linear
because Scalar is binary-spanned by 1 and omega. -/
def scalarOperator (h : H) : Module.End Scalar V where
  toFun := rho h
  map_add' := (rho h).map_add
  map_smul' a v := by
    have ha : a • v=a.re • v+a.im • (omega • v) := by
      calc
        a • v=(a.re • (1 : Scalar)+a.im • omega) • v :=
          congrArg (fun z : Scalar => z • v) (BinaryQuadraticField.scalar_eq a)
        _=a.re • v+a.im • (omega • v) := by simp only [add_smul,smul_assoc,one_smul]
    rw [ha,map_add,map_smul,map_smul,omega_commutes rho k hk hcentral]
    calc
      a.re • rho h v+a.im • (omega • rho h v)=
          (a.re • (1 : Scalar)+a.im • omega) • rho h v := by
        simp only [add_smul,smul_assoc,one_smul]
      _=a • rho h v := congrArg (fun z : Scalar => z • rho h v)
        (BinaryQuadraticField.scalar_eq a).symm

/-- The scalar representation has literally the same underlying action. -/
def representation : Representation Scalar H V where
  toFun := scalarOperator rho k hk hcentral
  map_one' := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) V => f v) rho.map_one
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) V => f v) (rho.map_mul g h)

@[simp] theorem representation_apply (h : H) (v : V) :
    representation rho k hk hcentral h v=rho h v := rfl

end SymmetricSubgroupAsymptotics.BinaryCubicScalarLinearRepresentation
