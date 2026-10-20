import SymmetricSubgroupAsymptotics.ModuleGeneratorProjectionSharing
import Mathlib.RepresentationTheory.Invariants

/-! Finite subgroup averaging separates fixed and moving generator rows.
The original acting group and its module are retained throughout. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace ModuleGeneratedBy

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The subgroup average, viewed as a scalar of the original group algebra. -/
def subgroupAverage (K : Subgroup G) [Fintype K]
    [Invertible (Fintype.card K : k)] : k[G] :=
  ⅟(Fintype.card K : k) • ∑ g : K, MonoidAlgebra.single (g : G) (1 : k)

lemma subgroupAverage_apply (rho : Representation k G V) (K : Subgroup G)
    [Fintype K] [Invertible (Fintype.card K : k)] (v : rho.asModule) :
    rho.asModuleEquiv (subgroupAverage (k := k) K • v) =
      (show Representation k K V from rho.comp K.subtype).averageMap (rho.asModuleEquiv v) := by
  rw [rho.asModuleEquiv_map_smul]
  simp [subgroupAverage, Representation.averageMap, GroupAlgebra.average,
    map_sum, Representation.asAlgebraHom_single_one,
    Representation.asAlgebraHom_of, MonoidHom.comp_apply,
    LinearMap.smul_apply, Finset.sum_apply]

/-- A fixed row and a row without subgroup invariants share generator positions.
Normality of the finite subgroup is unnecessary here: both rows are already
submodules for the full original acting group. -/
theorem of_subgroup_fixed_and_fixedFree (rho : Representation k G V)
    (K : Subgroup G) [Fintype K] [Invertible (Fintype.card K : k)]
    (P Q : Submodule k[G] rho.asModule)
    (hP : ∀ x : P, rho.asModuleEquiv (x : rho.asModule) ∈
      (show Representation k K V from rho.comp K.subtype).invariants)
    (hQ : ∀ x : Q, rho.asModuleEquiv (x : rho.asModule) ∈
      (show Representation k K V from rho.comp K.subtype).invariants → (x : rho.asModule) = 0)
    (hsup : P ⊔ Q = ⊤) (n : ℕ)
    (hgenP : ModuleGeneratedBy k[G] P n)
    (hgenQ : ModuleGeneratedBy k[G] Q n) :
    ModuleGeneratedBy k[G] rho.asModule n := by
  apply of_projected_submodules (R := k[G]) (M := rho.asModule) P Q (subgroupAverage (k := k) K) ?_ ?_
    hsup n hgenP hgenQ
  · intro x
    apply rho.asModuleEquiv.injective
    rw [subgroupAverage_apply]
    exact (show Representation k K V from rho.comp K.subtype).averageMap_id _ (hP x)
  · intro x
    let y : Q := ⟨subgroupAverage (k := k) K • (x : rho.asModule),
      Q.smul_mem _ x.property⟩
    apply hQ y
    change rho.asModuleEquiv
      (subgroupAverage (k := k) K • (x : rho.asModule)) ∈ _
    rw [subgroupAverage_apply]
    exact (show Representation k K V from rho.comp K.subtype).averageMap_invariant _

end ModuleGeneratedBy
end SymmetricSubgroupAsymptotics
