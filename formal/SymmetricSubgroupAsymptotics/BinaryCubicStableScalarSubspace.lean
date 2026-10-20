import SymmetricSubgroupAsymptotics.BinaryPlaneCubicScalarChart
import Mathlib.RepresentationTheory.Subrepresentation

/-! The scalar structure is recovered from the actual cubic operator.
The retained binary subspace and denominator keep their exact carriers;
no enlarged proxy space, complement, or capacity is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCubicStableScalarSubspace
open BinaryQuadraticField (Scalar omega)

variable {I : Type}

/-- Omega stability upgrades the SAME binary subspace to an F4 subspace. -/
def scalarSubspace (M : Submodule (ZMod 2) (I → Scalar))
    (hOmega : ∀ v∈M, (fun i => omega*v i)∈M) : Submodule Scalar (I → Scalar) where
  carrier := M
  zero_mem' := M.zero_mem
  add_mem' := M.add_mem
  smul_mem' a v hv := by
    have he : a • v = a.re • v + a.im • (fun i => omega*v i) := by
      funext i
      change a*v i = a.re • v i + a.im • (omega*v i)
      calc
        a*v i=(a.re • (1 : Scalar)+a.im • omega)*v i :=
          congrArg (fun z : Scalar => z*v i) (BinaryQuadraticField.scalar_eq a)
        _=a.re • v i+a.im • (omega*v i) := by
          simp only [add_mul,smul_mul_assoc,one_mul]
    rw [he]
    exact M.add_mem (M.smul_mem a.re hv) (M.smul_mem a.im (hOmega v hv))

@[simp] theorem mem_scalarSubspace (M : Submodule (ZMod 2) (I → Scalar))
    (hOmega : ∀ v∈M, (fun i => omega*v i)∈M) (v : I → Scalar) :
    v∈scalarSubspace M hOmega ↔ v∈M := Iff.rfl

variable {G V : Type} [Monoid G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A literal invariant binary subspace transported through an actual
cubic scalar chart is omega-stable, with no extra invariance hypothesis. -/
theorem transported_omega_stable (rho : Representation (ZMod 2) G V)
    (g : G) (E : V ≃ₗ[ZMod 2] (I → Scalar))
    (hE : ∀ v i, E (rho g v) i=omega*E v i)
    (S : Subrepresentation rho) :
    ∀ v∈S.toSubmodule.map E.toLinearMap, (fun i => omega*v i)∈
      S.toSubmodule.map E.toLinearMap := by
  rintro v ⟨w,hw,rfl⟩
  refine ⟨rho g w,S.apply_mem_toSubmodule g hw,?_⟩
  funext i
  exact hE w i

/-- The actual retained numerator or original denominator can each use
this construction; membership is still its literal transported membership. -/
def transportedScalarSubspace (rho : Representation (ZMod 2) G V)
    (g : G) (E : V ≃ₗ[ZMod 2] (I → Scalar))
    (hE : ∀ v i, E (rho g v) i=omega*E v i)
    (S : Subrepresentation rho) : Submodule Scalar (I → Scalar) :=
  scalarSubspace (S.toSubmodule.map E.toLinearMap)
    (transported_omega_stable rho g E hE S)

/-- Actual denominator inclusion survives the scalar upgrade exactly. -/
theorem transported_le (rho : Representation (ZMod 2) G V)
    (g : G) (E : V ≃ₗ[ZMod 2] (I → Scalar))
    (hE : ∀ v i, E (rho g v) i=omega*E v i)
    (D T : Subrepresentation rho) (hDT : D≤T) :
    transportedScalarSubspace rho g E hE D ≤ transportedScalarSubspace rho g E hE T := by
  rintro v ⟨w,hw,rfl⟩
  exact ⟨w,hDT hw,rfl⟩

end SymmetricSubgroupAsymptotics.BinaryCubicStableScalarSubspace
