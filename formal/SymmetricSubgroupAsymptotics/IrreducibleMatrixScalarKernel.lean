import SymmetricSubgroupAsymptotics.NormalInvariantLineEigenbasis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! The scalar subgroup on the original irreducible three-space is an
actual proper central normal subgroup. The matrix homomorphism below
uses the same representation and its chosen basis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.IrreducibleMatrixScalarKernel

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (b : Module.Basis (Fin 3) k V)

def matrixMap : G →* Matrix.GeneralLinearGroup (Fin 3) k where
  toFun g := {
    val := LinearMap.toMatrix b b (rho g)
    inv := LinearMap.toMatrix b b (rho g⁻¹)
    val_inv := by rw [←LinearMap.toMatrix_mul,←map_mul,mul_inv_cancel,map_one,
      LinearMap.toMatrix_one]
    inv_val := by rw [←LinearMap.toMatrix_mul,←map_mul,inv_mul_cancel,map_one,
      LinearMap.toMatrix_one] }
  map_one' := by
    apply Units.ext
    change LinearMap.toMatrix b b (rho 1)=1
    rw [map_one,LinearMap.toMatrix_one]
  map_mul' g h := by
    apply Units.ext
    change LinearMap.toMatrix b b (rho (g*h))=
      LinearMap.toMatrix b b (rho g)*LinearMap.toMatrix b b (rho h)
    rw [map_mul,LinearMap.toMatrix_mul]

theorem matrixMap_injective (hf : Function.Injective rho) :
    Function.Injective (matrixMap rho b) := by
  intro g h he
  apply hf
  apply (LinearMap.toMatrix b b).injective
  exact congrArg Units.val he

def scalars : Subgroup G :=
  (Subgroup.center (Matrix.GeneralLinearGroup (Fin 3) k)).comap (matrixMap rho b)

instance scalars_normal : (scalars rho b).Normal := by
  dsimp only [scalars]
  infer_instance

theorem mem_scalars_iff (g : G) :
    g∈scalars rho b ↔ ∃ a : k,rho g=a • (1 : Module.End k V) := by
  change matrixMap rho b g∈Subgroup.center _ ↔ _
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    change Matrix.scalar (Fin 3) a=LinearMap.toMatrix b b (rho g) at ha
    have he := congrArg (Matrix.toLin b b) ha
    simpa only [Matrix.toLin_toMatrix,Matrix.toLin_scalar] using he.symm
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    change Matrix.scalar (Fin 3) a=LinearMap.toMatrix b b (rho g)
    rw [ha]
    simpa only [Module.algebraMap_end_eq_smul_id] using
      (LinearMap.toMatrix_algebraMap b a).symm

theorem scalars_le_center (hf : Function.Injective rho) :
    scalars rho b≤Subgroup.center G := by
  intro z hz
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply matrixMap_injective rho b hf
  have he := Subgroup.mem_center_iff.mp hz (matrixMap rho b g)
  simpa only [map_mul] using he

theorem scalars_ne_top (hrho : Representation.IsIrreducible rho) :
    scalars rho b≠⊤ := by
  intro ht
  have hspan := NormalInvariantLineEigenbasis.orbit_span_eq_top rho hrho (b 0) (b.ne_zero 0)
  have horbit : Set.range (fun g : G => rho g (b 0))⊆
      Submodule.span k ({b 0} : Set V) := by
    rintro v ⟨g,rfl⟩
    obtain ⟨a,ha⟩ := (mem_scalars_iff rho b g).mp (by rw [ht]; trivial)
    change rho g (b 0)∈Submodule.span k ({b 0} : Set V)
    rw [ha]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
  have htop : Submodule.span k ({b 0} : Set V)=⊤ := by
    apply top_unique
    rw [←hspan]
    exact Submodule.span_le.mpr horbit
  have hm : b 1∈Submodule.span k ({b 0} : Set V) := by rw [htop]; trivial
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  have he := congrArg (fun v : V => b.repr v 1) ha
  simp at he

end SymmetricSubgroupAsymptotics.IrreducibleMatrixScalarKernel
