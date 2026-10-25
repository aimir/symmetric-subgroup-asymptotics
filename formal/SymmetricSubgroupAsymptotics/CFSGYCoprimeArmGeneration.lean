import SymmetricSubgroupAsymptotics.CFSGYArmProductPeriods
import SymmetricSubgroupAsymptotics.CommutingCoprimePeriodProductGeneration
import Mathlib.Tactic.FinCases

/-! Coprime compression of the SAME original Y arm products. These
structural generation lemmas retain explicit actual periods. The final
model instances must supply those periods from their genuine arm
lengths; no model endpoint assumes a head/generator bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGYCoprimeArmGeneration
open CFSG.Models.YGroups CFSGYArmProductGeneration CFSGYArmProductPeriods
open CommutingCoprimePeriodProductGeneration

private theorem eq_top_of_central_and_arms (arms : Arms)
    (H : Subgroup (CFSG.Models.YGroups.Group arms))
    (hr : PresentedGroup.of (rels := relations arms) none ∈ H)
    (ha : ∀ i, armProduct arms i ∈ H) : H = ⊤ := by
  apply top_unique
  rw [← fourGenerators_generate arms]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  refine Fin.cases ?_ ?_ i
  · exact hr
  · intro j
    exact ha j

/-- Two displayed noncentral elements, plus the original central involution. -/
def pairedArms (arms : Arms) (i j k : Fin 3) : Fin 2 → CFSG.Models.YGroups.Group arms :=
  ![armProduct arms i*armProduct arms j,armProduct arms k]

theorem paired_arms_generate (arms : Arms) (i j k : Fin 3) (hij : i ≠ j)
    (hcover : ∀ a : Fin 3, a = i ∨ a = j ∨ a = k)
    (m n : ℕ) (hcop : m.Coprime n)
    (hi : (armProduct arms i)^m = 1) (hj : (armProduct arms j)^n = 1) :
    Subgroup.closure (Set.range (pairedArms arms i j k) ∪
      {PresentedGroup.of (rels := relations arms) none}) = ⊤ := by
  let H := Subgroup.closure (Set.range (pairedArms arms i j k) ∪
    {PresentedGroup.of (rels := relations arms) none})
  have hr : PresentedGroup.of (rels := relations arms) none ∈ H :=
    Subgroup.subset_closure (Or.inr rfl)
  have hprod : armProduct arms i*armProduct arms j ∈ H :=
    Subgroup.subset_closure (Or.inl ⟨0,rfl⟩)
  have hk : armProduct arms k ∈ H := Subgroup.subset_closure (Or.inl ⟨1,rfl⟩)
  have hcomm := arm_products_commute arms i j hij
  have hiH := left_mem H _ _ m n hcop hcomm hi hj hprod
  have hjH := right_mem H _ _ m n hcop hcomm hi hj hprod
  apply eq_top_of_central_and_arms arms H hr
  intro a
  rcases hcover a with rfl | rfl | rfl
  · exact hiH
  · exact hjH
  · exact hk

/-- ONE displayed noncentral element, the product of all three arms. -/
def allArms (arms : Arms) : Fin 1 → CFSG.Models.YGroups.Group arms :=
  fun _ => armProduct arms 0*armProduct arms 1*armProduct arms 2

theorem all_arms_generate (arms : Arms) (m n k : ℕ)
    (hcop : m.Coprime n) (hcopLast : (m*n).Coprime k)
    (h0 : (armProduct arms 0)^m = 1) (h1 : (armProduct arms 1)^n = 1)
    (h2 : (armProduct arms 2)^k = 1) :
    Subgroup.closure (Set.range (allArms arms) ∪
      {PresentedGroup.of (rels := relations arms) none}) = ⊤ := by
  let H := Subgroup.closure (Set.range (allArms arms) ∪
    {PresentedGroup.of (rels := relations arms) none})
  have hr : PresentedGroup.of (rels := relations arms) none ∈ H :=
    Subgroup.subset_closure (Or.inr rfl)
  have hprod : (armProduct arms 0*armProduct arms 1)*armProduct arms 2 ∈ H :=
    Subgroup.subset_closure (Or.inl ⟨0,rfl⟩)
  have h01 := arm_products_commute arms (0 : Fin 3) 1 (by decide)
  have h02 := arm_products_commute arms (0 : Fin 3) 2 (by decide)
  have h12 := arm_products_commute arms (1 : Fin 3) 2 (by decide)
  have hp0 : (armProduct arms 0)^(m*n) = 1 := by rw [pow_mul,h0,one_pow]
  have hp1 : (armProduct arms 1)^(m*n) = 1 := by rw [Nat.mul_comm m n,pow_mul,h1,one_pow]
  have hp01 : (armProduct arms 0*armProduct arms 1)^(m*n) = 1 := by
    rw [h01.mul_pow,hp0,hp1,mul_one]
  have hcommLast := h02.mul_left h12
  have h01H := left_mem H _ _ (m*n) k hcopLast hcommLast hp01 h2 hprod
  have h2H := right_mem H _ _ (m*n) k hcopLast hcommLast hp01 h2 hprod
  have h0H := left_mem H _ _ m n hcop h01 h0 h1 h01H
  have h1H := right_mem H _ _ m n hcop h01 h0 h1 h01H
  apply eq_top_of_central_and_arms arms H hr
  intro a
  fin_cases a
  · exact h0H
  · exact h1H
  · exact h2H

end SymmetricSubgroupAsymptotics.CFSGYCoprimeArmGeneration
