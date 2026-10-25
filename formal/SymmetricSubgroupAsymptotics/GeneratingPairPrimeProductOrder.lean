import SymmetricSubgroupAsymptotics.CFSGTwoGenerationBasic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.FinCases

/-! A product of an actual generating pair cannot be trivial in a
noncommutative group. A literal prime product relator therefore supplies
an actual element of that prime order, and excludes faithful actions of
smaller degree. This uses neither a known model order nor a catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GeneratingPairPrimeProductOrder

variable {G : Type} [Group G]

theorem product_ne_one (g : Fin 2 → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hn : ¬ IsMulCommutative G) :
    g 0*g 1 ≠ 1 := by
  intro hxy
  have hy : g 1 = (g 0)⁻¹ := by
    calc g 1 = (g 0)⁻¹*(g 0*g 1) := (inv_mul_cancel_left _ _).symm
         _ = (g 0)⁻¹ := by rw [hxy,mul_one]
  have hle : (⊤ : Subgroup G) ≤ Subgroup.zpowers (g 0) := by
    rw [←hgen]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact Subgroup.mem_zpowers _
    · change g 1 ∈ Subgroup.zpowers (g 0)
      rw [hy]
      exact (Subgroup.zpowers (g 0)).inv_mem (Subgroup.mem_zpowers _)
  letI : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨g 0,le_antisymm le_top hle⟩
  exact hn inferInstance

theorem prime_dvd_card (g : Fin 2 → G)
    (hgen : Subgroup.closure (Set.range g) = ⊤) (hn : ¬ IsMulCommutative G)
    (p : ℕ) (hp : p.Prime) (hpow : (g 0*g 1)^p = 1) : p ∣ Nat.card G := by
  letI : Fact p.Prime := ⟨hp⟩
  have ho : orderOf (g 0*g 1) = p := orderOf_eq_prime hpow (product_ne_one g hgen hn)
  rw [←ho]
  exact orderOf_dvd_natCard _

theorem prime_dvd_presented_card (rels : List (FreeGroup (Fin 2)))
    (p : ℕ) (hp : p.Prime)
    (hrel : (FreeGroup.of (0 : Fin 2)*FreeGroup.of (1 : Fin 2))^p ∈ rels)
    (hn : ¬ IsMulCommutative (PresentedGroup {w | w ∈ rels})) :
    p ∣ Nat.card (PresentedGroup {w | w ∈ rels}) := by
  let g : Fin 2 → PresentedGroup {w | w ∈ rels} := PresentedGroup.of
  apply prime_dvd_card g (PresentedGroup.closure_range_of _) hn p hp
  have h := PresentedGroup.one_of_mem
    (rels := {w | w ∈ rels})
    (x := (FreeGroup.of (0 : Fin 2)*FreeGroup.of (1 : Fin 2))^p) hrel
  simpa only [g,map_pow,map_mul,PresentedGroup.of] using h

theorem degree_ge_of_prime_divisor {X : Type} [Finite X]
    (f : G →* Equiv.Perm X) (hf : Function.Injective f)
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Nat.card G) : p ≤ Nat.card X := by
  have hd : Nat.card G ∣ (Nat.card X).factorial := by
    simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective f hf
  exact hp.dvd_factorial.mp (hdiv.trans hd)

end SymmetricSubgroupAsymptotics.GeneratingPairPrimeProductOrder
