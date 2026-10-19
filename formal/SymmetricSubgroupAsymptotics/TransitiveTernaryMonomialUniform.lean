import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitUniform
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import Mathlib.GroupTheory.PGroup

/-! A transitive actual monomial action is cyclic over its full group
algebra. In characteristic three, an actual binary acting image makes
this bound uniform, even when no single block cycle is transitive. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.TransitiveTernaryMonomialUniform
variable {H I : Type} [Group H] [Fintype I] [DecidableEq I]
  (b : H →* Equiv.Perm I) (d : H → I → ZMod 3)
  (hone : ∀ i, d 1 i=1)
  (hmul : ∀ g h i, d (g*h) i=d g i*d h (b g⁻¹ i))

include hone hmul in
theorem generatedBy_one (i₀ : I) (htrans : ∀ i, ∃ g : H, b g i₀=i) :
    RepresentationGeneratedBy (TernaryMonomialOrbitUniform.representation b d hone hmul) 1 := by
  let rho := TernaryMonomialOrbitUniform.representation b d hone hmul
  let code : Fin 1 → rho.asModule := fun _ => rho.asModuleEquiv.symm (Pi.single i₀ 1)
  let P : Submodule (ZMod 3)[H] rho.asModule := Submodule.span (ZMod 3)[H] (Set.range code)
  let W : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hseed : (Pi.single i₀ (1 : ZMod 3) : I → ZMod 3)∈W := by
    change rho.asModuleEquiv.symm (Pi.single i₀ 1)∈P
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hdelta (i : I) : (Pi.single i (1 : ZMod 3) : I → ZMod 3)∈W := by
    obtain ⟨g,hg⟩ := htrans i
    have hm := W.apply_mem_toSubmodule g hseed
    change TernaryMonomialOrbitUniform.representation b d hone hmul g
      (Pi.single i₀ 1)∈W at hm
    rw [TernaryMonomialOrbitUniform.single,hg,mul_one] at hm
    have hn := W.toSubmodule.smul_mem ((d g i)⁻¹) hm
    rw [← Pi.single_smul,smul_eq_mul,
      inv_mul_cancel₀ (TernaryMonomialOrbitUniform.coefficient_ne_zero b d hone hmul g i)] at hn
    exact hn
  refine ⟨code,top_unique ?_⟩
  intro v _
  have hm := W.toSubmodule.sum_mem (fun i (_ : i∈Finset.univ) =>
    W.toSubmodule.smul_mem (rho.asModuleEquiv v i) (hdelta i))
  have he : (∑ i, rho.asModuleEquiv v i • (Pi.single i 1 : I → ZMod 3))=
      rho.asModuleEquiv v := by
    calc
      _=∑ i, Pi.single i (rho.asModuleEquiv v i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Pi.single_smul,smul_eq_mul,mul_one]
      _=rho.asModuleEquiv v := LinearMap.sum_single_apply _ _
  rw [he] at hm
  exact hm

include hone hmul in
theorem uniform_one [Finite H] (hH : IsPGroup 2 H)
    (i₀ : I) (htrans : ∀ i, ∃ g : H, b g i₀=i) :
    UniformSubrepresentationGeneratorBound
      (TernaryMonomialOrbitUniform.representation b d hone hmul) 1 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨n,hn⟩ := hH.exists_card_eq
  letI : NeZero (Nat.card H : ZMod 3) := ⟨by
    rw [hn,Nat.cast_pow]
    exact pow_ne_zero n (by decide +kernel)⟩
  exact RepresentationGeneratedBy.uniform_of_invertible_order _
    (generatedBy_one b d hone hmul i₀ htrans)

end SymmetricSubgroupAsymptotics.TransitiveTernaryMonomialUniform
