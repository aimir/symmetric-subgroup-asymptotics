import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi

/-! A common invariant prefix for actual leading generators bounds the
dimension of the entire module, including their lower coordinate terms.
This is a dimension estimate, not just a bound for the number of heads. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [FiniteDimensional k M] {n d : ℕ}

theorem finrank_le_of_leading_generators_in_invariant_prefix
    (C : M →ₗ[k] (Fin n → k)) (hC : Function.Injective C) (hdn : d≤n)
    (S : Finset M) (hspan : Submodule.span A (S : Set M)=⊤)
    (hlead : ∀ v∈S,∃ a : Fin n,a.val<d ∧ FiniteRowLeadingWeight.HasLeading (C v) a)
    (hstable : ∀ (r : A) (v : M),
      (∀ j : Fin n,d≤j.val → C v j=0) →
      ∀ j : Fin n,d≤j.val → C (r • v) j=0) :
    Module.finrank k M≤d := by
  have hall (v : M) : ∀ j : Fin n,d≤j.val → C v j=0 := by
    have hv : v∈Submodule.span A (S : Set M) := hspan.symm ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨a,ha,hvlead⟩ := hlead v hv
        intro j hj
        exact hvlead.2 j (by omega)
    | zero => simp only [map_zero,Pi.zero_apply,implies_true]
    | add v w _ _ hv hw =>
        intro j hj
        simp only [map_add,Pi.add_apply,hv j hj,hw j hj,zero_add]
    | smul r v _ hv => exact hstable r v hv
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
