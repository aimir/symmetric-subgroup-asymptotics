import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialMatrices
import Mathlib.GroupTheory.Perm.Fin
import Lean.Elab.Tactic.Omega

/-! Uniform actual coordinate cycles and their determinant-one signed
lifts. The proofs use the cycle length and sign, with no dimensional
case table. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeACyclicCoordinates
open CFSGTypeAMonomialMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

def weights (b : n) (σ : Equiv.Perm n) : n→F :=
  fun k => if k=b then (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : F) else 1

theorem weights_ne_zero (b : n) (σ : Equiv.Perm n) (k : n) : weights (F:=F) b σ k≠0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs|hs <;>
    by_cases hk : k=b <;> simp [weights,hs,hk]

omit [DecidableEq n] in
theorem predecessor_ne (hn : 2≤Fintype.card n)
    (σ : Equiv.Perm n) (hσ : σ.IsCycleOn (Finset.univ : Finset n)) (i : n) : i≠σ.symm i := by
  intro he
  have hh := (hσ.inv.pow_apply_eq (Finset.mem_univ i)).mp
    (show ((σ⁻¹)^1) i=i by simpa only [pow_one,Equiv.Perm.inv_def] using he.symm)
  rw [Finset.card_univ] at hh
  have hl := Nat.le_of_dvd (by decide : 0<1) hh
  omega

theorem finRotate_cycle (m : ℕ) (hm : 2≤m) :
    (finRotate m).IsCycleOn (Finset.univ : Finset (Fin m)) := by
  have he : {x : Fin m | finRotate m x≠x}=
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    ext x
    change (finRotate m x≠x)↔x∈((Finset.univ : Finset (Fin m)) : Set (Fin m))
    rw [←Equiv.Perm.mem_support,support_finRotate_of_le hm]
    rfl
  rw [←he]
  exact (isCycle_finRotate_of_le hm).isCycleOn

end SymmetricSubgroupAsymptotics.CFSGTypeACyclicCoordinates
