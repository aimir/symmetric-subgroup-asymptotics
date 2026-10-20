import SymmetricSubgroupAsymptotics.MarkedC4OrbitCutoffFamilies
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Solvable

/-! Actual subdirect orbit images for the ordinary socle-length step.
Indexing by ALL original points intentionally repeats equal orbits: the
socle-height maximum is unchanged, and no orbit partition or enumeration
hypothesis enters this construction. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.BoundedOrbitImages

variable {b : ℕ} (G : Subgroup (PermutationGroup b))

abbrev Fiber (x : Fin b) := MulAction.orbit G x
local instance (x : Fin b) : Fintype (Fiber G x) := Fintype.ofFinite _

def orbitAction (x : Fin b) : G →* Equiv.Perm (Fiber G x) :=
  MulAction.toPermHom G (Fiber G x)

abbrev Image (x : Fin b) := (orbitAction G x).range

def projection (x : Fin b) : G →* Image G x := (orbitAction G x).rangeRestrict

theorem projection_surjective (x : Fin b) : Function.Surjective (projection G x) :=
  (orbitAction G x).rangeRestrict_surjective

def subdirect : G →* ∀ x : Fin b, Image G x where
  toFun g x := projection G x g
  map_one' := by funext x; exact (projection G x).map_one
  map_mul' g h := by funext x; exact (projection G x).map_mul g h

/-- Recovery uses the image on the orbit containing the ORIGINAL point. -/
theorem subdirect_injective : Function.Injective (subdirect G) := by
  intro g h he
  apply Subtype.ext
  apply Equiv.ext
  intro x
  let y : Fiber G x := ⟨x,⟨1,by simp⟩⟩
  have hx := congrArg (fun f : ∀ x : Fin b, Image G x =>
    ((f x).val y).val) he
  exact hx

/-- Every factor is a quotient of the actual soluble source. -/
theorem image_solvable [IsSolvable G] (x : Fin b) : IsSolvable (Image G x) :=
  solvable_of_surjective (f := projection G x) (projection_surjective G x)

/-- The physical cutoff bounds EACH actual permutation image by the same
constant C!, independently of b and of the number of original orbits. -/
theorem image_card_le_factorial {C : ℕ}
    (hG : OrbitCutoffFamilies.OrbitCutoff C G) (x : Fin b) :
    Nat.card (Image G x) ≤ C.factorial := by
  have hi : Nat.card (Image G x) ≤ Nat.card (Equiv.Perm (Fiber G x)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hc : Fintype.card (Fiber G x) ≤ C := by
    simpa only [Nat.card_eq_fintype_card] using (hG x).le
  calc
    Nat.card (Image G x) ≤ Nat.card (Equiv.Perm (Fiber G x)) := hi
    _ = (Fintype.card (Fiber G x)).factorial := by
      rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    _ ≤ C.factorial := Nat.factorial_le hc

end SymmetricSubgroupAsymptotics.MarkedC4.BoundedOrbitImages
