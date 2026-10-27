import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Card

/-! A rigid base reduces an actual centralizer to images of cycle seeds.
All groups, permutations and powers remain literal. The finite assignment
set is a proof-certificate interface, not a supplied numerical class bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteBaseCentralizerSeedBounds

variable {G X T S : Type*} [Group G]

def baseEvaluation (rho : G →* Equiv.Perm X) (base : T ↪ X) (g : G) : T ↪ X :=
  base.trans (rho g).toEmbedding

theorem arbitrary_base_rigid (rho : G →* Equiv.Perm X) (base : T ↪ X)
    [Finite G] [Finite (T ↪ X)]
    (hbase : Function.Injective (baseEvaluation rho base))
    (hcard : Nat.card G = Nat.card (T ↪ X))
    (other : T ↪ X) (g h : G) (he : ∀ t, rho g (other t) = rho h (other t)) : g = h := by
  have hsurj : Function.Surjective (baseEvaluation rho base) :=
    ((Nat.bijective_iff_injective_and_card (baseEvaluation rho base)).mpr ⟨hbase,hcard⟩).2
  obtain ⟨s,hs⟩ := hsurj other
  have hpoint (t : T) : rho s (base t) = other t :=
    DFunLike.congr_fun hs t
  have hm : g*s = h*s := by
    apply hbase
    apply Function.Embedding.ext
    intro t
    change rho (g*s) (base t) = rho (h*s) (base t)
    rw [rho.map_mul,rho.map_mul]
    change rho g (rho s (base t)) = rho h (rho s (base t))
    rw [hpoint]
    exact he t
  exact mul_right_cancel hm

def seedEvaluation (rho : G →* Equiv.Perm X) (a : G) (seed : S → X)
    (g : Subgroup.centralizer ({a} : Set G)) : S → X := fun s => rho g.val (seed s)

theorem seed_evaluation_injective (rho : G →* Equiv.Perm X) (a : G)
    (base : T → X)
    (rigid : ∀ g h : G, (∀ t, rho g (base t) = rho h (base t)) → g = h)
    (seed : S → X)
    (covered : ∀ t, ∃ s : S, ∃ n : ℕ, base t = ((rho a)^n) (seed s)) :
    Function.Injective (seedEvaluation rho a seed) := by
  intro g h he
  apply Subtype.ext
  apply rigid
  intro t
  obtain ⟨s,n,ht⟩ := covered t
  have hg : Commute (rho g.val) (rho a) := by
    change rho g.val * rho a = rho a * rho g.val
    rw [←rho.map_mul,←rho.map_mul]
    exact congrArg rho (Subgroup.mem_centralizer_singleton_iff.mp g.property)
  have hh : Commute (rho h.val) (rho a) := by
    change rho h.val * rho a = rho a * rho h.val
    rw [←rho.map_mul,←rho.map_mul]
    exact congrArg rho (Subgroup.mem_centralizer_singleton_iff.mp h.property)
  have hseed : rho g.val (seed s) = rho h.val (seed s) := congrFun he s
  have hgp := congrArg (fun z : Equiv.Perm X => z (seed s)) (hg.pow_right n).eq
  have hhp := congrArg (fun z : Equiv.Perm X => z (seed s)) (hh.pow_right n).eq
  change rho g.val (((rho a)^n) (seed s)) = ((rho a)^n) (rho g.val (seed s)) at hgp
  change rho h.val (((rho a)^n) (seed s)) = ((rho a)^n) (rho h.val (seed s)) at hhp
  rw [ht,hgp,hhp,hseed]

theorem centralizer_card_le_seed_assignments (rho : G →* Equiv.Perm X) (a : G)
    (base : T → X)
    (rigid : ∀ g h : G, (∀ t, rho g (base t) = rho h (base t)) → g = h)
    (seed : S → X)
    (covered : ∀ t, ∃ s : S, ∃ n : ℕ, base t = ((rho a)^n) (seed s))
    (assignments : Finset (S → X))
    (allowed : ∀ g : Subgroup.centralizer ({a} : Set G),
      seedEvaluation rho a seed g ∈ assignments) :
    Nat.card (Subgroup.centralizer ({a} : Set G)) ≤ assignments.card := by
  let f : Subgroup.centralizer ({a} : Set G) → {v : S → X // v ∈ assignments} :=
    fun g => ⟨seedEvaluation rho a seed g,allowed g⟩
  have hf : Function.Injective f := by
    intro g h he
    exact seed_evaluation_injective rho a base rigid seed covered
      (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hf
  exact hc.trans_eq (by rw [Nat.card_eq_fintype_card,Fintype.card_coe])

end SymmetricSubgroupAsymptotics.FiniteBaseCentralizerSeedBounds
