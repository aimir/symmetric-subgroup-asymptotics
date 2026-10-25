import SymmetricSubgroupAsymptotics.SmallNoncommutativeCycleGauge
import SymmetricSubgroupAsymptotics.PermutationalWreathFinite
import Mathlib.Tactic.FinCases

/-! Base gauges on the literal permutational wreath product. The cycle
products are ordered, and the coefficient group may be noncommutative. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathCycleGaugeConjugacy
open SmallNoncommutativeCycleGauge
variable {C Q I : Type*} [Group C] [Group Q] [MulAction Q I]
abbrev W := PermutationalWreathProduct C Q I

theorem isConj_of_gauge (a b : W (C := C) (Q := Q) (I := I))
    (hq : a.right=b.right) (v : I → C)
    (hv : ∀ i, b.left i=v i*a.left i*(v (a.right⁻¹ • i))⁻¹) : IsConj a b := by
  apply isConj_iff.mpr
  refine ⟨⟨v,1⟩,?_⟩
  apply PermutationalWreathProduct.ext
  · funext i
    simpa only [PermutationalWreathProduct.mul_left,
      PermutationalWreathProduct.inv_left, PermutationalWreathProduct.mul_right,
      inv_one, one_smul, mul_one, one_mul, Pi.mul_apply, Pi.inv_apply] using (hv i).symm
  · simpa using hq

theorem isConj_of_identity_coordinates (a b : W (C := C) (Q := Q) (I := I))
    (ha : a.right=1) (hb : b.right=1)
    (h : ∀ i, IsConj (a.left i) (b.left i)) : IsConj a b := by
  choose v hv using fun i => isConj_iff.mp (h i)
  apply isConj_of_gauge a b (ha.trans hb.symm) v
  intro i
  simpa only [ha, inv_one, one_smul] using (hv i).symm

theorem isConj_of_pair_cycle (a b : W (C := C) (Q := Q) (I := I))
    (hq : a.right=b.right) (e : Fin 2 ≃ I)
    (h₀ : a.right⁻¹ • e 0=e 1) (h₁ : a.right⁻¹ • e 1=e 0)
    (h : IsConj (a.left (e 0)*a.left (e 1))
      (b.left (e 0)*b.left (e 1))) : IsConj a b := by
  obtain ⟨v₀,v₁,hv₀,hv₁⟩ := pair_gauge_of_product_isConj _ _ _ _ h
  let v : I → C := fun i => ![v₀,v₁] (e.symm i)
  apply isConj_of_gauge a b hq v
  intro i
  obtain ⟨j,rfl⟩ := e.surjective i
  fin_cases j
  · simpa [v,h₀] using hv₀
  · simpa [v,h₁] using hv₁

theorem isConj_of_triple_cycle (a b : W (C := C) (Q := Q) (I := I))
    (hq : a.right=b.right) (e : Fin 3 ≃ I)
    (h₀ : a.right⁻¹ • e 0=e 1) (h₁ : a.right⁻¹ • e 1=e 2)
    (h₂ : a.right⁻¹ • e 2=e 0)
    (h : IsConj (a.left (e 0)*a.left (e 1)*a.left (e 2))
      (b.left (e 0)*b.left (e 1)*b.left (e 2))) : IsConj a b := by
  obtain ⟨v₀,v₁,v₂,hv₀,hv₁,hv₂⟩ := triple_gauge_of_product_isConj _ _ _ _ _ _ h
  let v : I → C := fun i => ![v₀,v₁,v₂] (e.symm i)
  apply isConj_of_gauge a b hq v
  intro i
  obtain ⟨j,rfl⟩ := e.surjective i
  fin_cases j
  · simpa [v,h₀] using hv₀
  · simpa [v,h₁] using hv₁
  · simpa [v,h₂] using hv₂
end SymmetricSubgroupAsymptotics.WreathCycleGaugeConjugacy
