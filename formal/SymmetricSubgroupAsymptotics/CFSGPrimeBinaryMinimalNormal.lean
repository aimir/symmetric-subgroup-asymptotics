import SymmetricSubgroupAsymptotics.CFSGPrimeBinaryProductFactors
import SymmetricSubgroupAsymptotics.CFSGSurjectiveRepresentationIrreducible
import SymmetricSubgroupAsymptotics.PrimitiveSocleHomogeneousMinimalNormal
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! Literal minimal normal subgroups in the prime binary situation are
simple when nonabelian. In a nonsoluble source their actual ambient
centralizer is trivial. No almost-simple classification is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGPrimeBinaryMinimalNormal

variable {G V : Type} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Finite V]
  (rho : Representation (ZMod 2) G V)

theorem minimal_normal_isSimple
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : (Module.finrank (ZMod 2) V).Prime)
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card V - 1 = p)
    (E : Subgroup G) (hE : IsMinimalNormalSubgroup E)
    (hnc : ¬ IsMulCommutative E) : IsSimpleGroup E := by
  letI : E.Normal := hE.1
  have hEirr := CFSGCliffordBinaryPrimeDimension.normal_restriction_irreducible
    rho hrho hf hd E hE.2.1
  obtain ⟨C⟩ := PrimitiveSocleONanScottHelpers.chart_of_minimalNormal_nonempty E hE hnc
  let tau : Representation (ZMod 2) (Fin C.factorCount → C.Simple) V :=
    (rho.comp E.subtype).comp C.equiv.symm.toMonoidHom
  letI : Representation.IsIrreducible (rho.comp E.subtype) := hEirr
  letI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial
    (rho.comp E.subtype)
  have hti : Representation.IsIrreducible tau :=
    representationIrreducible_of_surjective_equivariant (rho.comp E.subtype) tau
      C.equiv.toMonoidHom (LinearMap.id) Function.surjective_id
      (by intro g v; change rho g v = rho (C.equiv.symm (C.equiv g)) v
          rw [C.equiv.symm_apply_apply]) hEirr
  have htf : Function.Injective tau := by
    intro a b hab
    apply C.equiv.symm.injective
    apply Subtype.ext
    exact hf hab
  letI : Subsingleton (Fin C.factorCount) :=
    CFSGPrimeBinaryProductFactors.factor_index_subsingleton tau hti htf hd hcard
      C.noncommutative
  letI : Unique (Fin C.factorCount) :=
    ⟨⟨0, C.factorCount_pos⟩, fun i => Subsingleton.elim _ _⟩
  exact (C.equiv.trans (MulEquiv.funUnique (Fin C.factorCount) C.Simple)).isSimpleGroup

theorem normal_centralizer_eq_bot_of_not_solvable
    (hrho : Representation.IsIrreducible rho) (hf : Function.Injective rho)
    (hd : (Module.finrank (ZMod 2) V).Prime)
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card V - 1 = p)
    (hns : ¬ IsSolvable G)
    (E : Subgroup G) [E.Normal] (hE : E ≠ ⊥) :
    Subgroup.centralizer (E : Set G) = ⊥ := by
  let D := Subgroup.centralizer (E : Set G)
  letI : Representation.IsIrreducible (rho.comp E.subtype) :=
    CFSGCliffordBinaryPrimeDimension.normal_restriction_irreducible rho hrho hf hd E hE
  letI : IsCyclic (CFSGIrreducibleLinearCentralizer.linearCentralizer
      (rho.comp E.subtype)) :=
    CFSGIrreducibleLinearCentralizer.centralizer_isCyclic_of_prime_nonzero_card
      (rho.comp E.subtype) hcard
  have hc (d : D) (e : E) : (d : G) * e = e * d :=
    (Subgroup.mem_centralizer_iff.mp d.2 e e.2).symm
  letI : IsCyclic D := isCyclic_of_injective
    (CFSGPrimeBinaryAbelianNormal.commutingSubgroupHom rho E D hc)
    (CFSGPrimeBinaryAbelianNormal.commutingSubgroupHom_injective rho hf E D hc)
  letI : IsMulCommutative D := ⟨⟨fun a b => mul_comm a b⟩⟩
  by_contra hD
  exact hns (CFSGPrimeBinaryAbelianNormal.soluble_of_nontrivial_abelian_normal
    rho hrho hf hd hcard D hD)

end SymmetricSubgroupAsymptotics.CFSGPrimeBinaryMinimalNormal
