import SymmetricSubgroupAsymptotics.DualGeneratorSchurCapacity
import SymmetricSubgroupAsymptotics.SemisimpleModuleGenerators
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Finite-dimensional contragredient duality preserves semisimplicity and
its ordinary module-generator bound.  The field may have modular
characteristic; no Maschke assumption is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.ZmudSemisimpleDualGenerators

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  (rho : Representation k G V)

/-- The invariant annihilator in the contragredient. -/
def annihilator (S : Subrepresentation rho) : Subrepresentation rho.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g l hl := by
    rw [Submodule.mem_dualAnnihilator] at hl ⊢
    intro v hv
    change l (rho g⁻¹ v) = 0
    exact hl _ (S.apply_mem_toSubmodule g⁻¹ hv)

/-- The invariant coannihilator in the original point module. -/
def coannihilator (S : Subrepresentation rho.dual) : Subrepresentation rho where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro l hl
    have he := hv (rho.dual g⁻¹ l) (S.apply_mem_toSubmodule g⁻¹ hl)
    change l (rho (g⁻¹)⁻¹ v) = 0 at he
    simpa only [inv_inv] using he

/-- Annihilation is the actual order-reversing duality of invariant
subspaces; its inverse is the original coannihilator. -/
def annihilatorOrderIso [FiniteDimensional k V] :
    Subrepresentation rho ≃o (Subrepresentation rho.dual)ᵒᵈ where
  toFun S := OrderDual.toDual (annihilator rho S)
  invFun S := coannihilator rho (OrderDual.ofDual S)
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv S := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := by
    intro S T
    change T.toSubmodule.dualAnnihilator ≤ S.toSubmodule.dualAnnihilator ↔
      S.toSubmodule ≤ T.toSubmodule
    exact Subspace.dualAnnihilator_le_dualAnnihilator_iff

/-- Complete reducibility of a finite-dimensional representation survives
contragredient duality even when the characteristic divides group order. -/
theorem dual_isSemisimple [FiniteDimensional k V]
    [IsSemisimpleModule k[G] rho.asModule] :
    IsSemisimpleModule k[G] rho.dual.asModule := by
  letI : ComplementedLattice (Subrepresentation rho) :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule rho).mpr
      inferInstance
  have hdual : ComplementedLattice (Subrepresentation rho.dual) :=
    (annihilatorOrderIso rho).dual.complementedLattice_iff.mp
      (inferInstance : ComplementedLattice (Subrepresentation rho)ᵒᵈ)
  exact (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
    rho.dual).mp hdual

/-- Evaluation is equivariant for the actual double contragredient. -/
def doubleDualEquiv [FiniteDimensional k V] : rho.Equiv rho.dual.dual :=
  Representation.Equiv.mk (Module.evalEquiv k V) (by
    intro g
    apply LinearMap.ext
    intro x
    ext f
    change f (rho g x) = f (rho (g⁻¹)⁻¹ x)
    rw [inv_inv])

/-- A semisimple finite-dimensional point module and its contragredient
admit the same upper bound on the number of generators. -/
theorem dual_generated [FiniteDimensional k V]
    [IsSemisimpleModule k[G] rho.asModule]
    {t : ℕ} (hgen : RepresentationGeneratedBy rho t) :
    RepresentationGeneratedBy rho.dual t := by
  letI : IsSemisimpleModule k[G] rho.dual.asModule := dual_isSemisimple rho
  have hdouble : RepresentationGeneratedBy rho.dual.dual t :=
    representationGeneratedBy_of_surjective rho rho.dual.dual
      (doubleDualEquiv rho).toIntertwiningMap (doubleDualEquiv rho).surjective hgen
  have hcap := representationSchurCapacity_le_of_dual_generated rho.dual t hdouble
  exact semisimple_representationGeneratedBy_of_schurCapacity_le rho.dual t hcap

end SymmetricSubgroupAsymptotics.ZmudSemisimpleDualGenerators
