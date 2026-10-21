import SymmetricSubgroupAsymptotics.LeadingGeneratorPrefixDimension
import Mathlib.RepresentationTheory.Subrepresentation

/-! Group-action preservation of a coefficient prefix supplies the
full group-algebra stability required by the leading-generator dimension
bound. The original representation and all lower terms are retained. -/
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
variable {k G M : Type} [Field k] [Group G] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] {n d : ℕ}

def coefficientPrefixPreimage (C : M →ₗ[k] (Fin n → k)) (d : ℕ) : Submodule k M where
  carrier := {v | ∀ j : Fin n,d≤j.val → C v j=0}
  zero_mem' := by
    intro j hj
    simp
  add_mem' := by
    intro x y hx hy j hj
    simp only [map_add,Pi.add_apply,hx j hj,hy j hj,zero_add]
  smul_mem' := by
    intro r v hv j hj
    simp only [map_smul,Pi.smul_apply,hv j hj,smul_zero]

omit [FiniteDimensional k M] in
theorem representation_leading_prefix_vanishes
    (rho : Representation k G M) (C : M →ₗ[k] (Fin n → k))
    (S : Finset rho.asModule) (hspan : Submodule.span k[G] (S : Set rho.asModule)=⊤)
    (hlead : ∀ v∈S,∃ a : Fin n,a.val<d ∧
      FiniteRowLeadingWeight.HasLeading (C (rho.asModuleEquiv v)) a)
    (hstable : ∀ (g : G) (v : M),
      (∀ j : Fin n,d≤j.val → C v j=0) →
      ∀ j : Fin n,d≤j.val → C (rho g v) j=0) :
    ∀ (v : M) (j : Fin n),d≤j.val → C v j=0 := by
  letI := Representation.instModuleMonoidAlgebraAsModule rho
  let P : Subrepresentation rho := {
    toSubmodule := coefficientPrefixPreimage C d
    apply_mem_toSubmodule g v hv := hstable g v hv }
  have hs : Submodule.span k[G] (S : Set rho.asModule)≤P.asSubmodule := by
    apply Submodule.span_le.mpr
    intro v hv j hj
    obtain ⟨a,ha,hleading⟩ := hlead v hv
    exact hleading.2 j (by omega)
  rw [hspan] at hs
  intro v
  exact hs (show rho.asModuleEquiv.symm v ∈ ⊤ from Submodule.mem_top)

theorem representation_finrank_le_of_leading_prefix
    (rho : Representation k G M) (C : M →ₗ[k] (Fin n → k))
    (hC : Function.Injective C) (hdn : d≤n)
    (S : Finset rho.asModule) (hspan : Submodule.span k[G] (S : Set rho.asModule)=⊤)
    (hlead : ∀ v∈S,∃ a : Fin n,a.val<d ∧
      FiniteRowLeadingWeight.HasLeading (C (rho.asModuleEquiv v)) a)
    (hstable : ∀ (g : G) (v : M),
      (∀ j : Fin n,d≤j.val → C v j=0) →
      ∀ j : Fin n,d≤j.val → C (rho g v) j=0) : Module.finrank k M≤d := by
  have hall := representation_leading_prefix_vanishes rho C S hspan hlead hstable
  let f : M →ₗ[k] (Fin d → k) := {
    toFun v j := C v ⟨j.val,lt_of_lt_of_le j.isLt hdn⟩
    map_add' v w := by funext j;exact congrFun (C.map_add v w) _
    map_smul' r v := by funext j;exact congrFun (C.map_smul r v) _ }
  have hf : Function.Injective f := by
    intro v w h
    apply hC
    funext j
    by_cases hj : j.val<d
    · exact congrFun h (⟨j.val,hj⟩ : Fin d)
    · rw [hall v j (by omega),hall w j (by omega)]
  have h := LinearMap.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using h

end SymmetricSubgroupAsymptotics
