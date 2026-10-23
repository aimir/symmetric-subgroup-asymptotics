import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Order.MinMax
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.BigOperators.Pi

/-! A dependent product over an involution splits into singleton and paired
orbit factors. The representative is the smaller index. This is literal
coordinate bookkeeping and does not assume a fixed-point lifting theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionOrbitProduct

variable {I : Type*} [LinearOrder I] [Fintype I]
variable (G : I → Type*) [∀ i, CommGroup (G i)]
variable (p : Equiv.Perm I) (hp : Function.Involutive p)

def representatives : Finset I := Finset.univ.filter (fun i => i ≤ p i)

def orbitFactor (c : ∀ i, G i) (i : I) : ∀ j, G j :=
  if p i = i then Pi.mulSingle i (c i)
  else Pi.mulSingle i (c i) * Pi.mulSingle (p i) (c (p i))

include hp

theorem representative_mem (j : I) : min j (p j) ∈ representatives p := by
  simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : j ≤ p j
  · simpa only [min_eq_left h] using h
  · rw [min_eq_right (le_of_not_ge h), hp]
    exact le_of_not_ge h

theorem orbitFactor_other (c : ∀ i, G i) (j i : I)
    (hi : i ∈ representatives p) (hne : i ≠ min j (p j)) :
    orbitFactor G p c i j = 1 := by
  have hrep : i ≤ p i := (Finset.mem_filter.mp hi).2
  have hij : i ≠ j := by
    intro h
    subst i
    exact hne (min_eq_left hrep).symm
  have hpij : p i ≠ j := by
    intro h
    have he : i = p j := by rw [← h, hp]
    have hj : p j ≤ j := by
      rw [he] at hrep
      rw [hp j] at hrep
      exact hrep
    exact hne (he.trans (min_eq_right hj).symm)
  unfold orbitFactor
  split_ifs <;> simp [Ne.symm hij, Ne.symm hpij]

theorem orbitFactor_representative (c : ∀ i, G i) (j : I) :
    orbitFactor G p c (min j (p j)) j = c j := by
  by_cases h : j ≤ p j
  · rw [min_eq_left h]
    by_cases he : p j = j
    · simp [orbitFactor, he]
    · simp [orbitFactor, he, Ne.symm he]
  · rw [min_eq_right (le_of_not_ge h)]
    have he : p j ≠ j := ne_of_lt (lt_of_not_ge h)
    have he' : j ≠ p j := Ne.symm he
    have hn : p (p j) ≠ p j := by
      rw [hp j]
      exact he'
    rw [orbitFactor, if_neg hn]
    change Pi.mulSingle (p j) (c (p j)) j * Pi.mulSingle (p (p j)) (c (p (p j))) j = c j
    rw [hp j]
    simp [he']

theorem product_orbitFactors (c : ∀ i, G i) :
    (∏ i ∈ representatives p, orbitFactor G p c i) = c := by
  funext j
  rw [Finset.prod_apply]
  rw [Finset.prod_eq_single_of_mem (min j (p j)) (representative_mem p hp j)]
  · exact orbitFactor_representative G p hp c j
  · intro i hi hne
    exact orbitFactor_other G p hp c j i hi hne

end SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionOrbitProduct
