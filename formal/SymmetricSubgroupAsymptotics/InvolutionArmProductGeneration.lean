import SymmetricSubgroupAsymptotics.OddInvolutionConjugateRecovery
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Group

/-! Literal recovery of an involutory arm from its product and the
preceding involution. At each step the preceding generator commutes
with all later arm factors. Conjugating it by the whole remaining
product therefore exposes only its adjacent braid conjugate, and the
checked odd-involution identity recovers the next generator.
No finiteness, presentation completeness or generator-count input is used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.InvolutionArmProductGeneration
variable {G : Type*} [Group G]

/-- The exact local relations along an arm, including its predecessor. -/
def Chain (s : G) : List G → Prop
  | [] => s^2 = 1
  | t::L => s^2 = 1 ∧ (t*s)^3 = 1 ∧ (∀ u ∈ L, Commute s u) ∧ Chain t L

private theorem head_square (s : G) (L : List G) (h : Chain s L) : s^2 = 1 := by
  cases L with
  | nil => exact h
  | cons t L => exact h.1

/-- The actual subgroup containing the predecessor and whole arm product
contains EVERY individual arm generator. -/
theorem members_mem_of_head_and_prod (H : Subgroup G) (s : G) (L : List G)
    (hchain : Chain s L) (hs : s ∈ H) (hprod : L.prod ∈ H) :
    ∀ u ∈ L, u ∈ H := by
  induction L generalizing s with
  | nil =>
    intro u hu
    cases hu
  | cons t L ih =>
    have hs2 : s^2 = 1 := hchain.1
    have htail : Chain t L := hchain.2.2.2
    have ht2 : t^2 = 1 := head_square t L htail
    have hcomm : Commute s L.prod := Commute.list_prod_right L s hchain.2.2.1
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ht2)
    have hword : (t*L.prod)*s*(t*L.prod)⁻¹ = t*s*t := by
      calc
        (t*L.prod)*s*(t*L.prod)⁻¹ = t*(L.prod*s*L.prod⁻¹)*t⁻¹ := by group
        _ = t*s*t := by rw [hcomm.symm.mul_inv_cancel,htinv]
    have hprod' : t*L.prod ∈ H := by simpa only [List.prod_cons] using hprod
    have hconj : t*s*t ∈ H := by
      rw [← hword]
      exact H.mul_mem (H.mul_mem hprod' hs) (H.inv_mem hprod')
    have ht : t ∈ H := OddInvolutionConjugateRecovery.mem_of_conjugate H t s 1
      ht2 hs2 hchain.2.1 hs hconj
    have hprodTail : L.prod ∈ H := by
      have hh := H.mul_mem (H.inv_mem ht) hprod'
      simpa only [inv_mul_cancel_left] using hh
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ht
    · exact ih t htail ht hprodTail u hu

end SymmetricSubgroupAsymptotics.InvolutionArmProductGeneration
