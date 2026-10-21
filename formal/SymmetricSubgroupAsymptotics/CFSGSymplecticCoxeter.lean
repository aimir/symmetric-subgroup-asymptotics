import SymmetricSubgroupAsymptotics.CFSGSymplecticSimpleWeylAction
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Range

/-! An actual ordered Coxeter word in the literal elementary C group.
The chain prefix is a list product, preserving the noncommutative order.
No permutation-group recognition is used in its definition. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def chainWeylAt (K : Type) [Field K] (r j : ℕ) : elementaryRootGroup K (r + 1) :=
  if h : j < r then simpleWeyl K (r + 1) (⟨j, Nat.lt_succ_of_lt h⟩ : Fin (r + 1)) else 1

def chainWeylPrefix (K : Type) [Field K] (r k : ℕ) : elementaryRootGroup K (r + 1) :=
  ((List.range k).map (chainWeylAt K r)).prod

def coxeterWeyl (K : Type) [Field K] (r : ℕ) : elementaryRootGroup K (r + 1) :=
  chainWeylPrefix K r r * simpleWeyl K (r + 1) (Fin.last r)

@[simp] theorem chainWeylPrefix_zero (K : Type) [Field K] (r : ℕ) :
    chainWeylPrefix K r 0 = 1 := rfl

theorem chainWeylPrefix_succ (K : Type) [Field K] (r k : ℕ) (hk : k < r) :
    chainWeylPrefix K r (k + 1) = chainWeylPrefix K r k *
      simpleWeyl K (r + 1) (⟨k, hk⟩ : Fin r).castSucc := by
  simp [chainWeylPrefix, List.range_succ, List.map_append, List.prod_append, chainWeylAt, hk]

def coordinateBasis (K : Type) [Field K] (r : ℕ) (side : Bool) (i : Fin (r + 1)) :
    Index (r + 1) → K := Pi.single (if side then Sum.inr i else Sum.inl i) 1

theorem simpleWeyl_chain_basis_left (K : Type) [Field K] (r : ℕ) (side : Bool) (i : Fin r) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ
      coordinateBasis K r side i.castSucc = coordinateBasis K r side i.succ := by
  cases side
  · exact simpleWeyl_chain_positive_left K r i
  · exact simpleWeyl_chain_negative_left K r i

theorem simpleWeyl_chain_basis_right (K : Type) [Field K] (r : ℕ) (side : Bool) (i : Fin r) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ
      coordinateBasis K r side i.succ = -coordinateBasis K r side i.castSucc := by
  cases side
  · exact simpleWeyl_chain_positive_right K r i
  · exact simpleWeyl_chain_negative_right K r i

theorem simpleWeyl_chain_basis_other (K : Type) [Field K] (r : ℕ) (side : Bool)
    (i : Fin r) (j : Fin (r + 1)) (hj : j ≠ i.castSucc) (hj' : j ≠ i.succ) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ
      coordinateBasis K r side j = coordinateBasis K r side j := by
  cases side
  · exact simpleWeyl_chain_other K r i (Sum.inl j)
      (fun h => hj (Sum.inl.inj h)) (fun h => hj' (Sum.inl.inj h))
      (by intro h; cases h) (by intro h; cases h)
  · exact simpleWeyl_chain_other K r i (Sum.inr j)
      (by intro h; cases h) (by intro h; cases h)
      (fun h => hj (Sum.inr.inj h)) (fun h => hj' (Sum.inr.inj h))

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
