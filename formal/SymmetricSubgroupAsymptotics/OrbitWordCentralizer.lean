import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Transitive orbit words force a commuting permutation from one image.
Only the finitely many possible images of the base point need certificates. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.OrbitWordCentralizer
variable {X J : Type}

def candidate (generator : J → Equiv.Perm X) (word : X → List J)
    (y x : X) : X := ((word x).map generator).prod y

theorem eq_one_or_of_orbit_words (generator : J → Equiv.Perm X)
    (base : X) (word : X → List J)
    (hword : ∀ x, ((word x).map generator).prod base=x)
    (z : Equiv.Perm X)
    (hcheck : ∀ y,
      (∀ j x, candidate generator word y (generator j x)=
        generator j (candidate generator word y x)) →
      (∀ x, candidate generator word y x=x) ∨
        (∀ x, candidate generator word y x=z x))
    (p : Equiv.Perm X) (hp : ∀ j, Commute p (generator j)) : p=1 ∨ p=z := by
  have hforce : ∀ x, p x=candidate generator word (p base) x := by
    intro x
    have hc : Commute p ((word x).map generator).prod :=
      Commute.list_prod_right _ p (by
        intro g hg
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
        exact hp j)
    calc
      p x=p (((word x).map generator).prod base) := by rw [hword]
      _=((word x).map generator).prod (p base) := congrArg (fun q : Equiv.Perm X => q base) hc.eq
      _=candidate generator word (p base) x := rfl
  have hcandidate : ∀ j x,
      candidate generator word (p base) (generator j x)=
        generator j (candidate generator word (p base) x) := by
    intro j x
    rw [←hforce,←hforce]
    exact congrArg (fun q : Equiv.Perm X => q x) (hp j).eq
  rcases hcheck (p base) hcandidate with hid | hz
  · left
    apply Equiv.ext
    intro x
    exact (hforce x).trans (hid x)
  · right
    apply Equiv.ext
    intro x
    exact (hforce x).trans (hz x)

end SymmetricSubgroupAsymptotics.OrbitWordCentralizer
