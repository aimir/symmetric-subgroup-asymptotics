import SymmetricSubgroupAsymptotics.BinaryFourPairFrameModel

/-!
# Merge the new E8 coordinate with all existing E8 occurrences

The selected four-pair construction produces one actual E8 factor and keeps
the old E8 coordinates inside its exterior.  This literal product chart puts
the new factor at the head of the same E8 occurrence family.  Every pair and
old E8 projection remains full and the entire remaining exterior image is
unchanged.  No product-fullness assumption is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryFourPairE8MergeModel

abbrev Sign := BinaryFourPairE8Model.Sign
abbrev E8 := BinaryFourPairE8Model.E8

variable {D : Type*} [Group D]

abbrev Source (n e : ℕ) :=
  E8 × ((Fin n → Sign) × ((Fin e → E8) × D))

abbrev Target (n e : ℕ) :=
  (Fin n → Sign) × ((Fin (e+1) → E8) × D)

/-- Put the newly fused E8 coordinate first and retain the old occurrence
order after it. -/
def mergeChart (n e : ℕ) : Source (D := D) n e ≃* Target (D := D) n e where
  toFun x := (x.2.1, (Fin.cases x.1 (fun j => x.2.2.1 j), x.2.2.2))
  invFun y := (y.2.1 0, (y.1, (fun j => y.2.1 j.succ, y.2.2)))
  left_inv x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext j
          rfl
        · rfl
  right_inv y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext k
        refine Fin.cases ?_ (fun j => ?_) k <;> rfl
      · rfl
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext k
        refine Fin.cases ?_ (fun j => ?_) k <;> rfl
      · rfl

def pairCoordinate (n e : ℕ) (j : Fin n) : Target (D := D) n e →* Sign where
  toFun x := x.1 j
  map_one' := rfl
  map_mul' _ _ := rfl

def e8Coordinate (n e : ℕ) (j : Fin (e+1)) : Target (D := D) n e →* E8 where
  toFun x := x.2.1 j
  map_one' := rfl
  map_mul' _ _ := rfl

def targetExterior (n e : ℕ) : Target (D := D) n e →* D where
  toFun x := x.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

def oldE8Coordinate (e : ℕ) (j : Fin e) : ((Fin e → E8) × D) →* E8 where
  toFun x := x.1 j
  map_one' := rfl
  map_mul' _ _ := rfl

def oldExterior (e : ℕ) : ((Fin e → E8) × D) →* D :=
  MonoidHom.snd (Fin e → E8) D

def OldPredicate (e : ℕ) (P : Subgroup D → Prop)
    (L : Subgroup ((Fin e → E8) × D)) : Prop :=
  (∀ j, L.map (oldE8Coordinate e j) = ⊤) ∧ P (L.map (oldExterior e))

abbrev CoverFamily (n e : ℕ) (P : Subgroup D → Prop) :=
  BinaryFourPairSelectedModel.CoverFamily (D := (Fin e → E8) × D) n
    (OldPredicate e P)

abbrev MergedFamily (n e : ℕ) (P : Subgroup D → Prop) :=
  {L : Subgroup (Target (D := D) n e) //
    (∀ j, L.map (pairCoordinate n e j) = ⊤) ∧
    (∀ j, L.map (e8Coordinate n e j) = ⊤) ∧
    P (L.map (targetExterior n e))}

@[simp] theorem mergeChart_new (n e : ℕ) (x : Source (D := D) n e) :
    (mergeChart n e x).2.1 0 = x.1 := rfl

@[simp] theorem mergeChart_old (n e : ℕ) (x : Source (D := D) n e) (j : Fin e) :
    (mergeChart n e x).2.1 j.succ = x.2.2.1 j := rfl

@[simp] theorem mergeChart_pair (n e : ℕ) (x : Source (D := D) n e) (j : Fin n) :
    (mergeChart n e x).1 j = x.2.1 j := rfl

@[simp] theorem mergeChart_exterior (n e : ℕ) (x : Source (D := D) n e) :
    (mergeChart n e x).2.2 = x.2.2.2 := rfl

theorem mergeChart_family_iff (n e : ℕ) (P : Subgroup D → Prop)
    (K : Subgroup (Source (D := D) n e)) :
    ((∀ j, (K.map (mergeChart n e).toMonoidHom).map (pairCoordinate n e j) = ⊤) ∧
      (∀ j, (K.map (mergeChart n e).toMonoidHom).map (e8Coordinate n e j) = ⊤) ∧
      P ((K.map (mergeChart n e).toMonoidHom).map (targetExterior n e))) ↔
    (K.map (MonoidHom.fst E8 ((Fin n → Sign) × ((Fin e → E8) × D))) = ⊤ ∧
      (∀ j, K.map (BinaryFourPairSelectedModel.retainedCoordinate j) = ⊤) ∧
      OldPredicate e P (K.map (BinaryFourPairSelectedModel.exterior n))) := by
  simp only [OldPredicate]
  constructor
  · rintro ⟨hp,h8,hD⟩
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [Subgroup.map_map] using h8 0
    · intro j
      simpa only [Subgroup.map_map] using hp j
    · intro j
      simpa only [Subgroup.map_map] using h8 j.succ
    · simpa only [Subgroup.map_map] using hD
  · rintro ⟨hnew,hp,hold,hD⟩
    refine ⟨?_,?_,?_⟩
    · intro j
      simpa only [Subgroup.map_map] using hp j
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa only [Subgroup.map_map] using hnew
      · simpa only [Subgroup.map_map] using hold k
    · simpa only [Subgroup.map_map] using hD

/-- Exact family equivalence; in particular, no extra pointing choice is
introduced when the new E8 coordinate joins the old occurrences. -/
def familyEquiv (n e : ℕ) (P : Subgroup D → Prop) :
    CoverFamily (D := D) n e P ≃ MergedFamily n e P :=
  (mergeChart n e).mapSubgroup.toEquiv.subtypeEquiv
    (fun K => by
      simpa only [MulEquiv.coe_mapSubgroup] using
        (mergeChart_family_iff n e P K).symm)

theorem family_card (n e : ℕ) (P : Subgroup D → Prop) :
    Nat.card (CoverFamily (D := D) n e P) = Nat.card (MergedFamily n e P) :=
  Nat.card_congr (familyEquiv n e P)

end SymmetricSubgroupAsymptotics.BinaryFourPairE8MergeModel
