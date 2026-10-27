import SymmetricSubgroupAsymptotics.InvolutionBraidTrace
import SymmetricSubgroupAsymptotics.CFSGYSectionEvenOrder
import Mathlib.Tactic.FinCases

/-! A literal common E6 node labeling and its actual Y braid semantics.
The proposed third A2 word is a definition only: its cube and its
commutations must be supplied by checked braid traces, not root images. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGYE6SelectedWords
open CFSG.Models.YGroups CFSGGeneration CFSGReduction
open InvolutionBraidTrace

def adjacent (i j : Fin 6) : Bool :=
  match i.val, j.val with
  | 0, 1 | 1, 0 | 1, 2 | 2, 1 | 0, 3 | 3, 0 | 3, 4 | 4, 3 | 0, 5 | 5, 0 => true
  | _, _ => false

def node (arms : Arms) (i : Fin 6) : Node arms :=
  ![none, near arms 0 0, near arms 0 1,
    near arms 1 0, near arms 1 1, near arms 2 0] i

def generator (arms : Arms) (i : Fin 6) : CFSG.Models.YGroups.Group arms :=
  PresentedGroup.of (rels := relations arms) (node arms i)

theorem node_injective (arms : Arms) : Function.Injective (node arms) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [node, near]

theorem adjacent_node (arms : Arms) (i j : Fin 6) :
    adjacent i j = true ↔ Adjacent arms (node arms i) (node arms j) := by
  fin_cases i <;> fin_cases j <;> simp [adjacent, node, near, Adjacent]

theorem generator_square (arms : Arms) (i : Fin 6) :
    generator arms i * generator arms i = 1 := by
  simpa only [pow_two] using y_generator_sq arms (node arms i)

theorem generator_commute (arms : Arms) (i j : Fin 6)
    (hij : adjacent i j = false) :
    generator arms i * generator arms j = generator arms j * generator arms i := by
  by_cases he : i = j
  · subst j
    rfl
  have hn : ¬Adjacent arms (node arms i) (node arms j) := by
    intro h
    have ht := (adjacent_node arms i j).mpr h
    rw [hij] at ht
    cases ht
  have hne : node arms i ≠ node arms j := fun h => he (node_injective arms h)
  have hp := y_nonadjacent_product_sq arms (node arms i) (node arms j) ⟨hne, hn⟩
  have hi : (generator arms i)⁻¹ = generator arms i :=
    inv_eq_of_mul_eq_one_right (generator_square arms i)
  have hj : (generator arms j)⁻¹ = generator arms j :=
    inv_eq_of_mul_eq_one_right (generator_square arms j)
  have ht : (generator arms i * generator arms j)⁻¹ =
      generator arms i * generator arms j :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)
  have he : generator arms j * generator arms i = generator arms i * generator arms j := by
    simpa only [mul_inv_rev, hi, hj] using ht
  exact he.symm

theorem generator_braid (arms : Arms) (i j : Fin 6)
    (hij : adjacent i j = true) :
    generator arms i * generator arms j * generator arms i =
      generator arms j * generator arms i * generator arms j := by
  let a := generator arms i
  let b := generator arms j
  have hc : (a * b) ^ 3 = 1 :=
    y_adjacent_product_cube arms (node arms i) (node arms j)
      ((adjacent_node arms i j).mp hij)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (generator_square arms i)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (generator_square arms j)
  have hi : (a * b * a)⁻¹ = a * b * a := by
    simp only [mul_inv_rev, hai, hbi, mul_assoc]
  have hm : (a * b * a) * (b * a * b) = 1 := by
    simpa only [pow_succ, pow_zero, mul_one, mul_assoc] using hc
  change a * b * a = b * a * b
  calc
    _ = (a * b * a)⁻¹ := hi.symm
    _ = (a * b * a)⁻¹ * ((a * b * a) * (b * a * b)) := by rw [hm, mul_one]
    _ = _ := by group

def wordA : List (Fin 6) := [1, 2]
def wordB : List (Fin 6) := [3, 4]

/-- A GUIDE-selected conjugator. No root-image calculation is used in
any proof in this file or in the braid verifier. -/
def guideW : List (Fin 6) := [5, 0, 3, 1, 0, 4, 3, 2, 1, 0]
def thetaWord : List (Fin 6) := guideW ++ [5] ++ guideW.reverse
def wordC : List (Fin 6) := [5] ++ thetaWord

def eval (arms : Arms) (w : List (Fin 6)) : CFSG.Models.YGroups.Group arms :=
  value (generator arms) w

theorem checked_trace_identity (arms : Arms) (w : List (Fin 6))
    (steps : List (Step (Fin 6))) (hcheck : check adjacent w steps = true) :
    eval arms w = 1 :=
  check_sound adjacent (generator arms) (generator_square arms)
    (generator_commute arms) (generator_braid arms) w steps hcheck

theorem abelianization_eval (arms : Arms) (w : List (Fin 6)) :
    Abelianization.of (eval arms w) =
      Abelianization.of (generator arms 0) ^ w.length := by
  induction w with
  | nil => simp [eval, value]
  | cons i tail ih =>
    change Abelianization.of (generator arms i * eval arms tail) = _
    rw [map_mul, ih]
    have hi : Abelianization.of (generator arms i) =
        Abelianization.of (generator arms 0) :=
      y_abelianization_generators_equal arms (node arms i)
    rw [hi]
    exact (pow_succ' (Abelianization.of (generator arms 0)) tail.length).symm

def derivedWord (arms : Arms) (w : List (Fin 6)) (hlen : Even w.length) :
    commutator (CFSG.Models.YGroups.Group arms) := by
  refine ⟨eval arms w, ?_⟩
  rw [← Abelianization.ker_of]
  change Abelianization.of (eval arms w) = 1
  rw [abelianization_eval]
  obtain ⟨k, hk⟩ := hlen
  have hs : Abelianization.of (generator arms 0) ^ 2 = 1 := by
    have hg : generator arms 0 ^ 2 = 1 := by
      simpa only [pow_two] using generator_square arms 0
    rw [← map_pow, hg, map_one]
  rw [hk, ← two_mul, pow_mul, hs, one_pow]

def derivedA (arms : Arms) := derivedWord arms wordA (by decide)
def derivedB (arms : Arms) := derivedWord arms wordB (by decide)
def derivedC (arms : Arms) := derivedWord arms wordC (by decide)

theorem derivedA_cube (arms : Arms) : derivedA arms ^ 3 = 1 := by
  apply Subtype.ext
  change eval arms wordA ^ 3 = 1
  have h := y_adjacent_product_cube arms (near arms 0 0) (near arms 0 1)
    (by simp [Adjacent, near])
  simpa [eval, wordA, value, generator, node] using h

theorem derivedB_cube (arms : Arms) : derivedB arms ^ 3 = 1 := by
  apply Subtype.ext
  change eval arms wordB ^ 3 = 1
  have h := y_adjacent_product_cube arms (near arms 1 0) (near arms 1 1)
    (by simp [Adjacent, near])
  simpa [eval, wordB, value, generator, node] using h

end SymmetricSubgroupAsymptotics.CFSGYE6SelectedWords
