import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! A permutation centralizing the original generators is determined by
one point image. Literal point-orbit words recover every other image;
only the degree-many candidate functions need scalar checks. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics
variable {X J : Type} (generators : J → Equiv.Perm X)

def pointWordPermutation (word : List J) : Equiv.Perm X := (word.map generators).prod

theorem centralizer_pointWord_commute (t : Equiv.Perm X)
    (ht : ∀ i,Commute t (generators i)) (word : List J) :
    Commute t (pointWordPermutation generators word) := by
  induction word with
  | nil => exact Commute.one_right t
  | cons i word ih =>
    change Commute t (generators i*pointWordPermutation generators word)
    exact (ht i).mul_right ih

theorem centralizer_eq_pointWord_candidate
    (base : X) (words : X → List J)
    (hwords : ∀ x,pointWordPermutation generators (words x) base=x)
    (t : Equiv.Perm X) (ht : ∀ i,Commute t (generators i)) (x : X) :
    t x=pointWordPermutation generators (words x) (t base) := by
  have he := congrArg (fun p : Equiv.Perm X => p base)
    (centralizer_pointWord_commute generators t ht (words x)).eq
  change t (pointWordPermutation generators (words x) base)=
    pointWordPermutation generators (words x) (t base) at he
  rwa [hwords x] at he

/-- The retained finite test is on candidate FUNCTIONS, so rejected
point images need not be extended to fictitious permutations. -/
theorem centralizer_base_mem_of_pointWord_candidates
    (base : X) (words : X → List J)
    (hwords : ∀ x,pointWordPermutation generators (words x) base=x)
    (allowed : Set X)
    (htest : ∀ y,(∀ i x,
      pointWordPermutation generators (words (generators i x)) y=
        generators i (pointWordPermutation generators (words x) y)) → y∈allowed)
    (t : Equiv.Perm X) (ht : ∀ i,Commute t (generators i)) :
    t base∈allowed := by
  apply htest
  intro i x
  rw [←centralizer_eq_pointWord_candidate generators base words hwords t ht,
    ←centralizer_eq_pointWord_candidate generators base words hwords t ht]
  exact congrArg (fun p : Equiv.Perm X => p x) (ht i).eq

end SymmetricSubgroupAsymptotics
