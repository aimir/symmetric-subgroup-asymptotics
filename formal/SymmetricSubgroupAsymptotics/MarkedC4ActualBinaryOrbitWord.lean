import SymmetricSubgroupAsymptotics.MarkedC4OrbitCutoffFamilies
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! A word constructed from the ACTUAL orbits of a binary permutation group.
Each letter is its actual transitive image, on canonical Fin coordinates.
The original group is identified with its actual subdirect image, so all
marked Hom weights are retained exactly. No tableau enumeration is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryOrbitWord

variable {b : ℕ} (G : Subgroup (PermutationGroup b))
abbrev Index := MulAction.orbitRel.Quotient G (Fin b)
local instance : Fintype (Index G) := Fintype.ofFinite _
abbrev Fiber (i : Index G) := MulAction.orbit G i.out
local instance (i : Index G) : Fintype (Fiber G i) := Fintype.ofFinite _

def degree (i : Index G) : ℕ := Fintype.card (Fiber G i)
def coordinate (i : Index G) : Fiber G i ≃ Fin (degree G i) := Fintype.equivFin _

/-- The point decomposition is constructed from the original orbit relation. -/
def pointCoordinates : Fin b ≃ Σ i : Index G,Fin (degree G i) :=
  (MulAction.selfEquivSigmaOrbits G (Fin b)).trans
    (Equiv.sigmaCongrRight (coordinate G))

theorem total_degree : ∑ i : Index G,degree G i = b := by
  have h := Fintype.card_congr (pointCoordinates G)
  simpa only [Fintype.card_fin,Fintype.card_sigma] using h.symm

theorem positive_degree (i : Index G) : 0 < degree G i := by
  letI : Nonempty (Fiber G i) := ⟨⟨i.out,MulAction.mem_orbit_self i.out⟩⟩
  exact Fintype.card_pos

theorem degree_lt {C : ℕ} (hG : OrbitCutoffFamilies.OrbitCutoff C G) (i : Index G) :
    degree G i < C := by
  simpa only [Nat.card_eq_fintype_card] using hG i.out

/-- The original permutation on an orbit, conjugated by its actual coordinate
bijection. This does not replace it by an abstract isomorphism type. -/
def letterMap (i : Index G) : G →* Equiv.Perm (Fin (degree G i)) :=
  (coordinate G i).permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Fiber G i))
abbrev Letter (i : Index G) := (letterMap G i).range

def projection (i : Index G) : G →* Letter G i := (letterMap G i).rangeRestrict

theorem projection_surjective (i : Index G) : Function.Surjective (projection G i) :=
  (letterMap G i).rangeRestrict_surjective

def map : G →* ∀ i : Index G,Letter G i where
  toFun g i := projection G i g
  map_one' := by funext i; exact (projection G i).map_one
  map_mul' g h := by funext i; exact (projection G i).map_mul g h

/-- The target is the literal subdirect subgroup, not the whole product. -/
abbrev WordImage := (map G).range

theorem letter_isPGroup (hG : IsPGroup 2 G) (i : Index G) : IsPGroup 2 (Letter G i) :=
  hG.of_surjective (projection G i) (projection_surjective G i)

/-- Every literal letter is transitive on its physical degree. -/
theorem letter_transitive (i : Index G) (a d : Fin (degree G i)) :
    ∃ g : Letter G i,g.val a=d := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G
    ((coordinate G i).symm a) ((coordinate G i).symm d)
  refine ⟨projection G i g,?_⟩
  have h := congrArg (coordinate G i) hg
  change coordinate G i (g • (coordinate G i).symm a)=d
  simpa only [Equiv.apply_symm_apply] using h

/-- The tuple acts separately on the actual canonical orbit coordinates. -/
def move (w : ∀ i : Index G,Letter G i)
    (z : Σ i : Index G,Fin (degree G i)) : Σ i : Index G,Fin (degree G i) :=
  ⟨z.1,(w z.1).val z.2⟩

theorem inverse_coordinate (z : Σ i : Index G,Fin (degree G i)) :
    (pointCoordinates G).symm z = ((coordinate G z.1).symm z.2).val := by
  rfl

/-- The label map transports the ORIGINAL action, including the original
positions and the same orbit labels; no abstract replacement action enters. -/
theorem point_equivariant (g : G) (x : Fin b) :
    pointCoordinates G (g.val x)=move G (map G g) (pointCoordinates G x) := by
  obtain ⟨z,rfl⟩ := (pointCoordinates G).symm.surjective x
  apply (pointCoordinates G).symm.injective
  rw [(pointCoordinates G).symm_apply_apply,(pointCoordinates G).apply_symm_apply]
  rw [inverse_coordinate,inverse_coordinate]
  change g.val (((coordinate G z.1).symm z.2).val)=
    ((coordinate G z.1).symm
      ((coordinate G z.1) (g • (coordinate G z.1).symm z.2))).val
  rw [Equiv.symm_apply_apply]
  rfl

/-- Faithfulness is read through the already constructed original-point
coordinate equivariance, so no conjugation implementation is unfolded. -/
theorem map_injective : Function.Injective (map G) := by
  intro g h he
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply (pointCoordinates G).injective
  rw [point_equivariant G g x,point_equivariant G h x,he]

def originalEquiv : G ≃* WordImage G := MonoidHom.ofInjective (map_injective G)

/-- The actual word image and the original label bijection recover literal
membership in the original subgroup of S_b. -/
theorem recover (f : PermutationGroup b) : f ∈ G ↔
    ∃ w : WordImage G, ∀ x : Fin b,
      pointCoordinates G (f x)=move G w.val (pointCoordinates G x) := by
  constructor
  · intro hf
    exact ⟨(map G).rangeRestrict ⟨f,hf⟩,point_equivariant G ⟨f,hf⟩⟩
  · rintro ⟨w,hw⟩
    obtain ⟨g,hg⟩ := w.property
    have he : f=g.val := by
      apply Equiv.ext
      intro x
      apply (pointCoordinates G).injective
      rw [hw x,point_equivariant]
      exact congrArg (fun u => move G u (pointCoordinates G x)) hg.symm
    exact he.symm ▸ g.property

/-- All r labelled C4 characters survive the constructed word reduction;
this equality is stronger than an unmarked source-cardinality comparison. -/
def homEquiv : (G →* Multiplicative (ZMod 4)) ≃
    (WordImage G →* Multiplicative (ZMod 4)) where
  toFun f := f.comp (originalEquiv G).symm.toMonoidHom
  invFun f := f.comp (originalEquiv G).toMonoidHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

theorem hom_card_eq : Nat.card (G →* Multiplicative (ZMod 4)) =
    Nat.card (WordImage G →* Multiplicative (ZMod 4)) := Nat.card_congr (homEquiv G)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryOrbitWord
