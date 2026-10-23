import SymmetricSubgroupAsymptotics.SubgroupProductClassBound
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum

/-! Real coordinate budgets for the SAME correlated finite group.
The integer class-count theorem applies to floors of the coordinate
budgets. In particular no monotonicity of class count under subgroup
inclusion, or independence of coordinate images, is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.ConjugacyClassRealCoordinateBound

theorem class_card_le_coordinate_product {ι : Type*} [Fintype ι]
    (V : ι→Type*) [∀i,Group (V i)] [∀i,Finite (V i)]
    (c : ι→ℝ) (hc0 : ∀i,0≤c i)
    (hc : ∀i (L : Subgroup (V i)),(Nat.card (ConjClasses L):ℝ)≤c i)
    (H : Type*) [Group H] [Finite H] (f : ∀i,H→*V i)
    (hf : Function.Injective (fun h i=>f i h)) :
    (Nat.card (ConjClasses H):ℝ)≤∏i,c i := by
  have hn : Nat.card (ConjClasses H)≤∏i,Nat.floor (c i) :=
    conjugacyClass_card_le_finite_coordinate_bounds V (fun i=>Nat.floor (c i))
      (fun i L=>(Nat.le_floor_iff (hc0 i)).mpr (hc i L)) H f hf
  have hcast : (Nat.card (ConjClasses H):ℝ)≤∏i,(Nat.floor (c i):ℝ) := by
    exact_mod_cast hn
  apply hcast.trans
  exact Finset.prod_le_prod (fun _ _=>Nat.cast_nonneg _) (fun i _=>Nat.floor_le (hc0 i))

end SymmetricSubgroupAsymptotics.ConjugacyClassRealCoordinateBound
