import SymmetricSubgroupAsymptotics.SubdirectTailImage
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.PUnit

/-! Ordered products of the actual finite binary carrier groups. Coordinate
fullness is defined by the original coordinate homomorphisms, and peeling
records the literal suffix image rather than the whole suffix product. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryCarrierWord

/-- A factor stores its actual group, with no classification or recognition data. -/
structure Factor where
  Carrier : Type
  [group : Group Carrier]
  [finite : Finite Carrier]
  binary : IsPGroup 2 Carrier

attribute [instance] Factor.group Factor.finite

def Product : List Factor → Type
  | [] => PUnit.{1}
  | A :: w => A.Carrier × Product w

instance productGroup : (w : List Factor) → Group (Product w)
  | [] => inferInstanceAs (Group PUnit.{1})
  | A :: w =>
      letI := productGroup w
      inferInstanceAs (Group (A.Carrier × Product w))

instance productFinite : (w : List Factor) → Finite (Product w)
  | [] => inferInstanceAs (Finite PUnit.{1})
  | A :: w =>
      letI := productFinite w
      inferInstanceAs (Finite (A.Carrier × Product w))

theorem product_binary (w : List Factor) : IsPGroup 2 (Product w) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction w with
  | nil => exact IsPGroup.of_card (n := 0) (by simp [Product])
  | cons A w ih =>
      obtain ⟨a,ha⟩ := A.binary.exists_card_eq
      obtain ⟨b,hb⟩ := ih.exists_card_eq
      apply IsPGroup.of_card (n := a+b)
      change Nat.card (A.Carrier × Product w) = 2^(a+b)
      rw [Nat.card_prod,ha,hb,pow_add]

/-- A typed position retains the actual factor occurring in the word. -/
inductive Slot : List Factor → Factor → Type 1
  | head {A : Factor} {w : List Factor} : Slot (A :: w) A
  | tail {A B : Factor} {w : List Factor} : Slot w B → Slot (A :: w) B

def projection : {w : List Factor} → {A : Factor} →
    Slot w A → Product w →* A.Carrier
  | _, _, .head => MonoidHom.fst _ _
  | _, _, .tail i => (projection i).comp (MonoidHom.snd _ _)

/-- Fullness means onto every original factor, allowing all correlations. -/
def Full (w : List Factor) (H : Subgroup (Product w)) : Prop :=
  ∀ (A : Factor) (i : Slot w A), Function.Surjective ((projection i).comp H.subtype)

abbrev Family (w : List Factor) := {H : Subgroup (Product w) // Full w H}

theorem full_nil (H : Subgroup (Product [])) : Full [] H := by
  intro A i
  cases i

/-- The suffix condition concerns exactly H.map snd. This equivalence is
proved from the coordinate maps, not adopted as a counting recurrence. -/
theorem full_cons_iff (A : Factor) (w : List Factor)
    (H : Subgroup (Product (A :: w))) :
    Full (A :: w) H ↔
      Function.Surjective (Prod.fst ∘ H.subtype) ∧
        Full w (SubdirectTailImage.tail H) := by
  constructor
  · intro h
    refine ⟨h A .head,?_⟩
    intro B i
    exact SubdirectTailImage.tail_coordinate_surjective H (projection i)
      (h B (.tail i))
  · rintro ⟨hfirst,htail⟩ B i
    cases i with
    | head => exact hfirst
    | tail i =>
        intro b
        obtain ⟨y,hy⟩ := htail B i b
        obtain ⟨x,hx,hxy⟩ := y.2
        refine ⟨⟨x,hx⟩,?_⟩
        change projection i x.2 = b
        change projection i (y : Product w) = b at hy
        have he : x.2 = (y : Product w) := hxy
        exact (congrArg (projection i) he).trans hy

def first (A : Factor) (w : List Factor) (H : Family (A :: w)) :
    SubdirectTailImage.FirstFull A.Carrier (Product w) :=
  ⟨H.1,((full_cons_iff A w H.1).mp H.2).1⟩

def tail (A : Factor) (w : List Factor) (H : Family (A :: w)) : Family w :=
  ⟨SubdirectTailImage.tail H.1,((full_cons_iff A w H.1).mp H.2).2⟩

/-- The exact selected-tail family before any counting or enlargement. -/
abbrev PeelFamily (A : Factor) (w : List Factor) :=
  {H : SubdirectTailImage.FirstFull A.Carrier (Product w) //
    Full w (SubdirectTailImage.tail H.1)}

def familyPeelEquiv (A : Factor) (w : List Factor) :
    Family (A :: w) ≃ PeelFamily A w where
  toFun H := ⟨first A w H,(tail A w H).2⟩
  invFun H := ⟨H.1.1,(full_cons_iff A w H.1.1).mpr ⟨H.1.2,H.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem familyPeelEquiv_val (A : Factor) (w : List Factor)
    (H : Family (A :: w)) : (familyPeelEquiv A w H).1.1 = H.1 := rfl

instance subgroupFinite (w : List Factor) : Finite (Subgroup (Product w)) :=
  Finite.of_injective (fun H : Subgroup (Product w) => (H : Set (Product w)))
    SetLike.coe_injective

instance familyFinite (w : List Factor) : Finite (Family w) := inferInstance

end BinaryCarrierWord
end SymmetricSubgroupAsymptotics
