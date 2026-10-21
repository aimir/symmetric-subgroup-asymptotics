import SymmetricSubgroupAsymptotics.LeadingTermMinimalGenerators
import SymmetricSubgroupAsymptotics.FiniteRowLeadingWeight
import Mathlib.Algebra.Algebra.Tower

/-! Minimum-weight generators prohibit cancellation by any actual algebra
operator applied to another retained generator. The prohibition retains
both original vectors, beyond a relation on their leading labels. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable {k A M : Type} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    {n d : ℕ}

theorem exists_minimum_generators_no_actual_leading_collision
    (hd : ModuleGeneratedBy A M d) (C : M →ₗ[k] (Fin n → k))
    (hC : Function.Injective C) (a0 : Fin n) :
    ∃ (v : Fin d → M) (label : Fin d → Fin n),
      Submodule.span A (Set.range v) = ⊤ ∧
      (∀ i, v i ≠ 0 → FiniteRowLeadingWeight.HasLeading (C (v i)) (label i)) ∧
      (∀ i j, i ≠ j → v i ≠ 0 → v j ≠ 0 → ∀ r : A,
        ¬FiniteRowLeadingWeight.HasLeading (C (r • v i)) (label j)) := by
  obtain ⟨v, hv, hmin⟩ := LeadingTermMinimalGenerators.exists_minimum_weight
    d hd (fun x => FiniteRowLeadingWeight.weight (C x))
  have hex (i : Fin d) (hi : v i ≠ 0) :
      ∃ a, FiniteRowLeadingWeight.HasLeading (C (v i)) a :=
    FiniteRowLeadingWeight.exists_leading
      (fun he => hi (hC (he.trans (map_zero C).symm)))
  let label : Fin d → Fin n := fun i => if hi : v i ≠ 0 then (hex i hi).choose else a0
  have hl (i : Fin d) (hi : v i ≠ 0) :
      FiniteRowLeadingWeight.HasLeading (C (v i)) (label i) := by
    simpa only [label, dif_pos hi] using (hex i hi).choose_spec
  refine ⟨v, label, hv, hl, ?_⟩
  intro i j hij _hi hj r hr
  let c : k := C (v j) (label j) / C (r • v i) (label j)
  have he : c * C (r • v i) (label j) = C (v j) (label j) := div_mul_cancel₀ _ hr.1
  have hs : FiniteRowLeadingWeight.HasLeading (c • C (r • v i)) (label j) := by
    constructor
    · change c * C (r • v i) (label j) ≠ 0
      rw [he]
      exact (hl j hj).1
    · intro b hb
      change c * C (r • v i) b = 0
      rw [hr.2 b hb, mul_zero]
  have hdrop := FiniteRowLeadingWeight.cancellation_decreases_weight hs (hl j hj) he
  have hact : C ((c • r) • v i) = c • C (r • v i) := by
    rw [smul_assoc, map_smul]
  apply LeadingTermMinimalGenerators.no_lower_weight_cancellation d
    (fun x => FiniteRowLeadingWeight.weight (C x)) v hv hmin j i hij (c • r)
  rw [map_sub, hact]
  exact hdrop

end SymmetricSubgroupAsymptotics
