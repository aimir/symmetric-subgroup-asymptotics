import Mathlib.Algebra.Group.Conj
import Mathlib.SetTheory.Cardinal.Finite

/-! A sparse upper certificate for the conjugacy-class count of an actual group.
Every element is covered by the original row map. Representatives and conjugators
are indices in that same map; no ambient-group conjugacy is substituted for
conjugacy inside the source group. Distinct representatives are not required.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] {n : ℕ}

/-- Complete original rows, at most `c` representative labels, and one
original-group conjugator per row. The conjugacy equation avoids inverses,
so a permutation instance can check it pointwise using two products. -/
structure FiniteConjugacyCover (rows : Fin n → G) (c : ℕ) where
  complete : Function.Surjective rows
  representative : Fin c → Fin n
  label : Fin n → Fin c
  conjugator : Fin n → Fin n
  conjugates : ∀ i,
    rows (conjugator i) * rows i =
      rows (representative (label i)) * rows (conjugator i)

namespace FiniteConjugacyCover

variable {rows : Fin n → G} {c : ℕ}

/-- The class assigned to one of the supplied representative labels. -/
def classMap (C : FiniteConjugacyCover rows c) (j : Fin c) : ConjClasses G :=
  ConjClasses.mk (rows (C.representative j))

theorem row_isConj (C : FiniteConjugacyCover rows c) (i : Fin n) :
    IsConj (rows i) (rows (C.representative (C.label i))) := by
  apply isConj_iff.mpr
  exact ⟨rows (C.conjugator i), mul_inv_eq_iff_eq_mul.mpr (C.conjugates i)⟩

/-- Coverage is of all original conjugacy classes, even when representative
labels repeat or different labels represent the same class. -/
theorem classMap_surjective (C : FiniteConjugacyCover rows c) :
    Function.Surjective C.classMap := by
  intro q
  obtain ⟨g, hg⟩ := ConjClasses.exists_rep q
  obtain ⟨i, hi⟩ := C.complete g
  refine ⟨C.label i, ?_⟩
  change ConjClasses.mk (rows (C.representative (C.label i))) = q
  calc
    _ = ConjClasses.mk (rows i) :=
      (ConjClasses.mk_eq_mk_iff_isConj.mpr (C.row_isConj i)).symm
    _ = q := by rw [hi]; exact hg

/-- A complete sparse cover gives the stated upper class-count bound. -/
theorem card_conjClasses_le (C : FiniteConjugacyCover rows c) :
    Nat.card (ConjClasses G) ≤ c := by
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_surjective C.classMap C.classMap_surjective

theorem card_conjClasses_le_of_le (C : FiniteConjugacyCover rows c)
    {b : ℕ} (hcb : c ≤ b) : Nat.card (ConjClasses G) ≤ b :=
  C.card_conjClasses_le.trans hcb

/-- Verify the sparse equations through an injective homomorphism, for example
the subtype map of an original permutation group. All representatives and
conjugators remain original elements through `rows`; the ambient group supplies
only a faithful way of checking the equations. -/
def ofInjectiveMap {H : Type*} [Group H]
    (rows : Fin n → G) (complete : Function.Surjective rows)
    (f : G →* H) (hf : Function.Injective f)
    (representative : Fin c → Fin n) (label : Fin n → Fin c)
    (conjugator : Fin n → Fin n)
    (hconjugates : ∀ i,
      f (rows (conjugator i)) * f (rows i) =
        f (rows (representative (label i))) * f (rows (conjugator i))) :
    FiniteConjugacyCover rows c where
  complete := complete
  representative := representative
  label := label
  conjugator := conjugator
  conjugates i := by
    apply hf
    simpa only [map_mul] using hconjugates i

end FiniteConjugacyCover
end SymmetricSubgroupAsymptotics

end
