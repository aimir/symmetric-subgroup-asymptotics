import SymmetricSubgroupAsymptotics.BinaryCarrierWord

/-! The ordered carrier product is the dependent product of its literal
occurrences. Each coordinate is the original factor at that list position.
Map/comap preserves whole subgroups and arbitrary original predicates; no
permutation of occurrences or quotient by repeated types is introduced.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

/-- The original typed slot at a numerical list position. -/
def slotAt : (w : List Factor) → (i : Fin w.length) → Slot w (w.get i)
  | [], i => Fin.elim0 i
  | _ :: w, i => Fin.cases .head (fun j => .tail (slotAt w j)) i

abbrev CoordinateProduct (w : List Factor) :=
  (i : Fin w.length) → (w.get i).Carrier

/-- Every coordinate is the already-defined original slot projection. -/
def coordinateMap (w : List Factor) : Product w →* CoordinateProduct w where
  toFun x i := projection (slotAt w i) x
  map_one' := by funext i; exact map_one (projection (slotAt w i))
  map_mul' x y := by funext i; exact map_mul (projection (slotAt w i)) x y

@[simp] theorem coordinateMap_apply (w : List Factor) (x : Product w)
    (i : Fin w.length) : coordinateMap w x i = projection (slotAt w i) x := rfl

@[simp] theorem coordinateMap_cons_zero (A : Factor) (w : List Factor)
    (x : Product (A :: w)) : coordinateMap (A :: w) x 0 = x.1 := rfl

@[simp] theorem coordinateMap_cons_succ (A : Factor) (w : List Factor)
    (x : Product (A :: w)) (i : Fin w.length) :
    coordinateMap (A :: w) x i.succ = coordinateMap w x.2 i := rfl

def fromCoordinates : (w : List Factor) → CoordinateProduct w → Product w
  | [], _ => PUnit.unit
  | _ :: w, f => (f 0, fromCoordinates w (fun i => f i.succ))

theorem fromCoordinates_coordinateMap (w : List Factor) :
    ∀ x : Product w, fromCoordinates w (coordinateMap w x) = x := by
  induction w with
  | nil =>
      intro x
      change (PUnit.unit : PUnit.{1}) = x
      exact Subsingleton.elim _ _
  | cons A w ih =>
      intro x
      apply Prod.ext
      · rfl
      · change fromCoordinates w (coordinateMap w x.2) = x.2
        exact ih x.2

theorem coordinateMap_fromCoordinates (w : List Factor) :
    ∀ f : CoordinateProduct w, coordinateMap w (fromCoordinates w f) = f := by
  induction w with
  | nil => intro f; funext i; exact Fin.elim0 i
  | cons A w ih =>
      intro f
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (ih (fun j => f j.succ)) j

/-- A genuine group equivalence with the actual dependent occurrence
product, including the empty list. -/
def coordinateEquiv (w : List Factor) : Product w ≃* CoordinateProduct w where
  toFun := coordinateMap w
  invFun := fromCoordinates w
  left_inv := fromCoordinates_coordinateMap w
  right_inv := coordinateMap_fromCoordinates w
  map_mul' := (coordinateMap w).map_mul

@[simp] theorem coordinateEquiv_apply (w : List Factor) (x : Product w)
    (i : Fin w.length) : coordinateEquiv w x i = projection (slotAt w i) x := rfl

/-- Numerical positions and typed slots test exactly the same fullness. -/
theorem full_iff_coordinate_surjective (w : List Factor)
    (H : Subgroup (Product w)) :
    Full w H ↔ ∀ i : Fin w.length,
      Function.Surjective (fun h : H => coordinateMap w h.1 i) := by
  constructor
  · intro h i
    exact h (w.get i) (slotAt w i)
  · intro h
    induction w with
    | nil => exact full_nil H
    | cons A w ih =>
        apply (full_cons_iff A w H).mpr
        refine ⟨h 0,?_⟩
        apply ih
        intro i
        exact SubdirectTailImage.tail_coordinate_surjective H
          (fun x => coordinateMap w x i) (h i.succ)

def CoordinateFull (w : List Factor) (K : Subgroup (CoordinateProduct w)) : Prop :=
  ∀ i : Fin w.length, Function.Surjective (fun k : K => k.1 i)

theorem coordinateFull_map_iff (w : List Factor) (H : Subgroup (Product w)) :
    CoordinateFull w (H.map (coordinateEquiv w).toMonoidHom) ↔ Full w H := by
  rw [full_iff_coordinate_surjective]
  constructor
  · intro h i u
    obtain ⟨k,hk⟩ := h i u
    obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp k.2
    refine ⟨⟨x,hx⟩,?_⟩
    exact (congrFun he i).trans hk
  · intro h i u
    obtain ⟨x,hx⟩ := h i u
    exact ⟨⟨coordinateEquiv w x.1,Subgroup.mem_map.mpr ⟨x.1,x.2,rfl⟩⟩,hx⟩

/-- The target predicate is tested on the literal inverse image. This
keeps arbitrary original survival and weight definitions on the same H. -/
def coordinateFamilyEquiv (w : List Factor)
    (P : Subgroup (Product w) → Prop) :
    {H : Family w // P H.1} ≃
      {K : Subgroup (CoordinateProduct w) // CoordinateFull w K ∧
        P (K.comap (coordinateEquiv w).toMonoidHom)} where
  toFun H :=
    ⟨H.1.1.map (coordinateEquiv w).toMonoidHom,
      (coordinateFull_map_iff w H.1.1).mpr H.1.2,by
        rw [Subgroup.comap_map_eq_self_of_injective
          (f := (coordinateEquiv w).toMonoidHom) (coordinateEquiv w).injective]
        exact H.2⟩
  invFun K :=
    ⟨⟨K.1.comap (coordinateEquiv w).toMonoidHom,by
      apply (coordinateFull_map_iff w _).mp
      rw [Subgroup.map_comap_eq_self_of_surjective
        (f := (coordinateEquiv w).toMonoidHom) (coordinateEquiv w).surjective]
      exact K.2.1⟩,K.2.2⟩
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective (coordinateEquiv w).injective H.1.1
  right_inv K := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self_of_surjective (coordinateEquiv w).surjective K.1

theorem coordinateFamilyEquiv_reconstruct (w : List Factor)
    (P : Subgroup (Product w) → Prop) (H : {H : Family w // P H.1}) :
    (coordinateFamilyEquiv w P H).1.comap (coordinateEquiv w).toMonoidHom = H.1.1 :=
  Subgroup.comap_map_eq_self_of_injective (coordinateEquiv w).injective H.1.1

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
