import SymmetricSubgroupAsymptotics.FiniteBaseCentralizerSeedBounds
import Mathlib.Data.Fintype.Pi

/-! Computable point assignments for equal-length cycle seeds. A commuting
permutation preserves exact periods and different cycles. Combined with a
rigid base covered by the seed cycles, their finite assignment set bounds
the SAME actual centralizer. No numerical capacity is an input. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.FinitePermutationCycleSeedAssignments
open FiniteBaseCentralizerSeedBounds

variable {X : Type*} {r : ℕ}

def CycleSeparated (pi : Equiv.Perm X) (d : ℕ) (v : Fin r → X) : Prop :=
  (∀ i, (pi^d) (v i) = v i) ∧
  (∀ i, ∀ k : Fin d, k.val ≠ 0 → (pi^k.val) (v i) ≠ v i) ∧
  (∀ i j, i ≠ j → ∀ k : Fin d, (pi^k.val) (v i) ≠ v j)

instance [DecidableEq X] (pi : Equiv.Perm X) (d : ℕ) (v : Fin r → X) :
    Decidable (CycleSeparated pi d v) := by
  unfold CycleSeparated
  infer_instance

def assignments [Fintype X] [DecidableEq X] (pi : Equiv.Perm X) (d r : ℕ) :
    Finset (Fin r → X) := Finset.univ.filter (CycleSeparated pi d)

theorem maps_cycle_separated (pi sigma : Equiv.Perm X) (d : ℕ)
    (hc : Commute sigma pi) (v : Fin r → X) (hv : CycleSeparated pi d v) :
    CycleSeparated pi d (fun i => sigma (v i)) := by
  rcases hv with ⟨hperiod,hminimal,hapart⟩
  have hpoint (n : ℕ) (x : X) : sigma ((pi^n) x) = (pi^n) (sigma x) := by
    exact congrArg (fun z : Equiv.Perm X => z x) (hc.pow_right n).eq
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [←hpoint,hperiod]
  · intro i k hk he
    apply hminimal i k hk
    apply sigma.injective
    rw [hpoint]
    exact he
  · intro i j hij k he
    apply hapart i j hij k
    apply sigma.injective
    rw [hpoint]
    exact he

variable {G : Type*} [Group G]

theorem seed_images_mem [Fintype X] [DecidableEq X]
    (rho : G →* Equiv.Perm X) (a : G) (d : ℕ) (seed : Fin r → X)
    (hseed : CycleSeparated (rho a) d seed)
    (g : Subgroup.centralizer ({a} : Set G)) :
    seedEvaluation rho a seed g ∈ assignments (rho a) d r := by
  have hc : Commute (rho g.val) (rho a) := by
    change rho g.val * rho a = rho a * rho g.val
    rw [←rho.map_mul,←rho.map_mul]
    exact congrArg rho (Subgroup.mem_centralizer_singleton_iff.mp g.property)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  exact maps_cycle_separated (rho a) (rho g.val) d hc seed hseed

theorem centralizer_card_le_assignments [Fintype X] [DecidableEq X]
    {T : Type*} (rho : G →* Equiv.Perm X) (a : G)
    (base : T → X)
    (rigid : ∀ g h : G, (∀ t, rho g (base t) = rho h (base t)) → g = h)
    (d : ℕ) (seed : Fin r → X)
    (covered : ∀ t, ∃ i : Fin r, ∃ n : ℕ, base t = ((rho a)^n) (seed i))
    (hseed : CycleSeparated (rho a) d seed) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) ≤ (assignments (rho a) d r).card :=
  centralizer_card_le_seed_assignments rho a base rigid seed covered
    (assignments (rho a) d r) (seed_images_mem rho a d seed hseed)

end SymmetricSubgroupAsymptotics.FinitePermutationCycleSeedAssignments
