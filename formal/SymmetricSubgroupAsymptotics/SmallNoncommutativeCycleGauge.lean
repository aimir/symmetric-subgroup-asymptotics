import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

/-! Ordered cycle products classify the base gauges on cycles of length
two and three for arbitrary groups. No commutativity or bound on element
centralizer orders is assumed. These are the noncommutative leaves of
the small full-wreath conjugacy code. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SmallNoncommutativeCycleGauge
variable {C : Type*} [Group C]

theorem pair_gauge_of_product_isConj (a₀ a₁ b₀ b₁ : C)
    (h : IsConj (a₀*a₁) (b₀*b₁)) :
    ∃ v₀ v₁ : C, b₀=v₀*a₀*v₁⁻¹ ∧ b₁=v₁*a₁*v₀⁻¹ := by
  obtain ⟨u,hu⟩ := isConj_iff.mp h
  refine ⟨u,b₀⁻¹*u*a₀,?_,?_⟩
  · group
  · calc
      b₁=b₀⁻¹*(b₀*b₁) := by group
      _ = b₀⁻¹*(u*(a₀*a₁)*u⁻¹) := by rw [hu]
      _ = _ := by group

theorem pair_product_isConj_iff (a₀ a₁ b₀ b₁ : C) :
    IsConj (a₀*a₁) (b₀*b₁) ↔
      ∃ v₀ v₁ : C, b₀=v₀*a₀*v₁⁻¹ ∧ b₁=v₁*a₁*v₀⁻¹ := by
  constructor
  · exact pair_gauge_of_product_isConj a₀ a₁ b₀ b₁
  · rintro ⟨v₀,v₁,rfl,rfl⟩
    exact isConj_iff.mpr ⟨v₀,by group⟩

theorem triple_gauge_of_product_isConj (a₀ a₁ a₂ b₀ b₁ b₂ : C)
    (h : IsConj (a₀*a₁*a₂) (b₀*b₁*b₂)) :
    ∃ v₀ v₁ v₂ : C, b₀=v₀*a₀*v₁⁻¹ ∧ b₁=v₁*a₁*v₂⁻¹ ∧ b₂=v₂*a₂*v₀⁻¹ := by
  obtain ⟨u,hu⟩ := isConj_iff.mp h
  refine ⟨u,b₀⁻¹*u*a₀,b₁⁻¹*b₀⁻¹*u*a₀*a₁,?_,?_,?_⟩
  · group
  · group
  · calc
      b₂=b₁⁻¹*b₀⁻¹*(b₀*b₁*b₂) := by group
      _ = b₁⁻¹*b₀⁻¹*(u*(a₀*a₁*a₂)*u⁻¹) := by rw [hu]
      _ = _ := by group

theorem triple_product_isConj_iff (a₀ a₁ a₂ b₀ b₁ b₂ : C) :
    IsConj (a₀*a₁*a₂) (b₀*b₁*b₂) ↔
      ∃ v₀ v₁ v₂ : C, b₀=v₀*a₀*v₁⁻¹ ∧ b₁=v₁*a₁*v₂⁻¹ ∧ b₂=v₂*a₂*v₀⁻¹ := by
  constructor
  · exact triple_gauge_of_product_isConj a₀ a₁ a₂ b₀ b₁ b₂
  · rintro ⟨v₀,v₁,v₂,rfl,rfl,rfl⟩
    exact isConj_iff.mpr ⟨v₀,by group⟩

end SymmetricSubgroupAsymptotics.SmallNoncommutativeCycleGauge
