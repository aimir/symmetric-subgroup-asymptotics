import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesSelectedTop
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite lists of actual transitive point sets for weighted orbit induction.
Their coordinate homomorphism keeps all correlations in the original group. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences

/-- A finite list of nonempty actual point sets. -/
inductive ActionShape : Type 1 where
  | nil : ActionShape
  | cons (X : Type) [Fintype X] [Nonempty X] (tail : ActionShape) : ActionShape

namespace ActionShape

abbrev Coordinates : ActionShape → Type
  | .nil => PUnit
  | @ActionShape.cons X _ _ tail => Equiv.Perm X × Coordinates tail

@[reducible] instance coordinatesGroup : (S : ActionShape) → Group S.Coordinates
  | .nil => by change Group PUnit; infer_instance
  | @ActionShape.cons X _ _ tail => by
      change Group (Equiv.Perm X × Coordinates tail)
      letI := coordinatesGroup tail
      infer_instance

instance coordinatesFinite : (S : ActionShape) → Finite S.Coordinates
  | .nil => by change Finite PUnit; infer_instance
  | @ActionShape.cons X _ _ tail => by
      change Finite (Equiv.Perm X × Coordinates tail)
      letI := coordinatesFinite tail
      infer_instance

def degree : ActionShape → ℕ
  | .nil => 0
  | @ActionShape.cons X _ _ tail => Fintype.card X + tail.degree

def weight (v : ℕ → ℝ) : ActionShape → ℝ
  | .nil => 0
  | @ActionShape.cons X _ _ tail => v (Fintype.card X) + tail.weight v

variable {G : Type} [Group G]

def head {X : Type} [Fintype X] [Nonempty X] {S : ActionShape}
    (f : G →* (cons X S).Coordinates) : G →* Equiv.Perm X :=
  (MonoidHom.fst _ _).comp f

def tail {X : Type} [Fintype X] [Nonempty X] {S : ActionShape}
    (f : G →* (cons X S).Coordinates) : G →* S.Coordinates :=
  (MonoidHom.snd _ _).comp f

/-- Every component is transitive under its actual original image. -/
def TransitiveProfile : {S : ActionShape} → (G →* S.Coordinates) → Prop
  | .nil, _ => True
  | @ActionShape.cons X _ _ _S, f =>
      (letI : MulAction G X := MulAction.compHom X (head f)
       MulAction.IsPretransitive G X) ∧ TransitiveProfile (tail f)

/-- A head point set of size one contributes no faithfulness: all actual
source information remains in the tail coordinates. -/
theorem tail_injective_of_subsingleton
    {X : Type} [Fintype X] [Nonempty X] [Subsingleton X]
    {S : ActionShape} (f : G →* (cons X S).Coordinates)
    (hf : Function.Injective f) : Function.Injective (tail f) := by
  intro g h hgh
  apply hf
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · exact hgh

/-- The nil shape has no faithful nontrivial source. -/
theorem subsingleton_of_nil (f : G →* nil.Coordinates)
    (hf : Function.Injective f) : Subsingleton G :=
  ⟨fun _g _h => hf (Subsingleton.elim _ _)⟩

/-- Restrict a dependent permutation product to its tail coordinates. -/
def finTail {n : ℕ} (X : Fin (n + 1) → Type) :
    (∀ i, Equiv.Perm (X i)) →* ∀ i : Fin n, Equiv.Perm (X i.succ) where
  toFun g i := g i.succ
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Package a finite dependent family of original point sets as a list. -/
def ofFamily : (n : ℕ) → (X : Fin n → Type) →
    [∀ i, Fintype (X i)] → [∀ i, Nonempty (X i)] → ActionShape
  | 0, _, _, _ => .nil
  | n + 1, X, _, _ => .cons (X 0) (ofFamily n (fun i => X i.succ))

/-- The original joint homomorphism, reassociated into the chosen list. -/
def familyHom : (n : ℕ) → (X : Fin n → Type) →
    [∀ i, Fintype (X i)] → [∀ i, Nonempty (X i)] →
    (G →* ∀ i, Equiv.Perm (X i)) → G →* (ofFamily n X).Coordinates
  | 0, _, _, _, _ => 1
  | n + 1, X, _, _, f =>
      ((Pi.evalMonoidHom (fun i => Equiv.Perm (X i)) 0).comp f).prod
        (familyHom n (fun i => X i.succ) ((finTail X).comp f))

/-- Reassociation preserves the exact original equality of all coordinates. -/
theorem familyHom_eq_iff (n : ℕ) (X : Fin n → Type)
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (f : G →* ∀ i, Equiv.Perm (X i)) (g h : G) :
    familyHom n X f g = familyHom n X f h ↔ f g = f h := by
  induction n with
  | zero => simp [familyHom, funext_iff]
  | succ n ih =>
    constructor
    · intro he
      have hh := congrArg Prod.fst he
      have ht := congrArg Prod.snd he
      have ht' := (ih (fun i => X i.succ) ((finTail X).comp f)).mp ht
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hh
      · exact congrFun ht' j
    · intro he
      apply Prod.ext
      · exact congrFun he 0
      · exact (ih (fun i => X i.succ) ((finTail X).comp f)).mpr
          (congrArg (fun z => finTail X z) he)

theorem familyHom_injective (n : ℕ) (X : Fin n → Type)
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (f : G →* ∀ i, Equiv.Perm (X i)) (hf : Function.Injective f) :
    Function.Injective (familyHom n X f) :=
  fun g h he => hf ((familyHom_eq_iff n X f g h).mp he)

end ActionShape
end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
