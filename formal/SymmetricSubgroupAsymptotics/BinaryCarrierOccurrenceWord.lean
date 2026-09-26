import SymmetricSubgroupAsymptotics.BinaryCarrierWordCoordinates
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.Equiv.Basic

/-! An explicitly enumerated original occurrence product is an ordered
word in exactly those factors. The enumeration changes only positions;
it neither identifies repeated factors nor changes their group structures.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOccurrenceWord

open BinaryCarrierWord

/-- Transport only along equality of the entire original Factor. -/
def factorCongr {A B : Factor} (h : A = B) : A.Carrier ≃* B.Carrier := by
  cases h
  exact MulEquiv.refl _

/-- Pull back dependent coordinates along an actual enumeration. The
inverse casts only along its proved inverse equations. -/
def reindexFactors {α β : Type} (F : β → Factor) (e : α ≃ β) :
    ((b : β) → (F b).Carrier) ≃* ((a : α) → (F (e a)).Carrier) :=
  { (Equiv.piCongrLeft (fun b => (F b).Carrier) e).symm with
    map_mul' := fun _ _ => rfl }

@[simp] theorem reindexFactors_symm_apply {α β : Type}
    (F : β → Factor) (e : α ≃ β)
    (f : (a : α) → (F (e a)).Carrier) (a : α) :
    (reindexFactors F e).symm f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply (fun b => (F b).Carrier) e f a

def reindexedWordEquiv (w : List Factor) {κ : Type} (F : κ → Factor)
    (e : Fin w.length ≃ κ) (hF : ∀ i, w.get i = F (e i)) :
    Product w ≃* ((k : κ) → (F k).Carrier) :=
  ((coordinateEquiv w).trans (MulEquiv.piCongrRight (fun i => factorCongr (hF i)))).trans
    (reindexFactors F e).symm

theorem reindexedWordEquiv_apply (w : List Factor) {κ : Type} (F : κ → Factor)
    (e : Fin w.length ≃ κ) (hF : ∀ i, w.get i = F (e i))
    (x : Product w) (i : Fin w.length) :
    reindexedWordEquiv w F e hF x (e i) = factorCongr (hF i) (coordinateMap w x i) :=
  reindexFactors_symm_apply F e _ i

def IndexedFull {κ : Type} (F : κ → Factor)
    (K : Subgroup ((k : κ) → (F k).Carrier)) : Prop :=
  ∀ k, Function.Surjective (fun x : K => x.1 k)

theorem indexedFull_map_iff (w : List Factor) {κ : Type} (F : κ → Factor)
    (e : Fin w.length ≃ κ) (hF : ∀ i, w.get i = F (e i))
    (H : Subgroup (Product w)) :
    IndexedFull F (H.map (reindexedWordEquiv w F e hF).toMonoidHom) ↔ Full w H := by
  rw [full_iff_coordinate_surjective]
  constructor
  · intro h i u
    obtain ⟨x,hx⟩ := h (e i) (factorCongr (hF i) u)
    obtain ⟨y,hy,he⟩ := Subgroup.mem_map.mp x.2
    refine ⟨⟨y,hy⟩,?_⟩
    apply (factorCongr (hF i)).injective
    exact (reindexedWordEquiv_apply w F e hF y i).symm.trans
      ((congrFun he (e i)).trans hx)
  · intro h k u
    obtain ⟨i,rfl⟩ := e.surjective k
    obtain ⟨x,hx⟩ := h i ((factorCongr (hF i)).symm u)
    change coordinateMap w x.1 i = (factorCongr (hF i)).symm u at hx
    refine ⟨⟨reindexedWordEquiv w F e hF x.1,
      Subgroup.mem_map.mpr ⟨x.1,x.2,rfl⟩⟩,?_⟩
    change reindexedWordEquiv w F e hF x.1 (e i) = u
    rw [reindexedWordEquiv_apply, hx]
    exact (factorCongr (hF i)).apply_symm_apply u

variable {ι : Type} (F : ι → Factor) (m : ι → ℕ) {n : ℕ}
    (e : Fin n ≃ (Σ i, Fin (m i)))

/-- The explicit enumeration fixes one occurrence at every word position. -/
def occurrenceWord : List Factor := List.ofFn (fun j => F (e j).1)

@[simp] theorem occurrenceWord_length : (occurrenceWord F m e).length = n :=
  List.length_ofFn

def occurrenceEnumeration : Fin (occurrenceWord F m e).length ≃ (Σ i, Fin (m i)) :=
  (finCongr (occurrenceWord_length F m e)).trans e

theorem occurrenceWord_get (j : Fin (occurrenceWord F m e).length) :
    (occurrenceWord F m e).get j = F (occurrenceEnumeration F m e j).1 :=
  List.get_ofFn (fun j => F (e j).1) j

abbrev OccurrenceProduct := (i : ι) → Fin (m i) → (F i).Carrier

/-- Currying keeps the factor label and the original occurrence label. -/
def curryOccurrences :
    ((o : Σ i, Fin (m i)) → (F o.1).Carrier) ≃* OccurrenceProduct F m :=
  { Equiv.piCurry (fun i (_ : Fin (m i)) => (F i).Carrier) with
    map_mul' := fun _ _ => rfl }

def occurrenceEquiv : Product (occurrenceWord F m e) ≃* OccurrenceProduct F m :=
  (reindexedWordEquiv (occurrenceWord F m e) (fun o : Σ i, Fin (m i) => F o.1)
    (occurrenceEnumeration F m e) (occurrenceWord_get F m e)).trans
      (curryOccurrences F m)

/-- Exact projection at the original occurrence selected by j. The only
transport is the proved equality of the original Factor at that position. -/
theorem occurrenceEquiv_apply (x : Product (occurrenceWord F m e))
    (j : Fin (occurrenceWord F m e).length) :
    occurrenceEquiv F m e x (occurrenceEnumeration F m e j).1
        (occurrenceEnumeration F m e j).2 =
      factorCongr (occurrenceWord_get F m e j)
        (coordinateMap (occurrenceWord F m e) x j) :=
  reindexedWordEquiv_apply (occurrenceWord F m e)
    (fun o : Σ i, Fin (m i) => F o.1)
    (occurrenceEnumeration F m e) (occurrenceWord_get F m e) x j

def OccurrenceFull (K : Subgroup (OccurrenceProduct F m)) : Prop :=
  ∀ i (j : Fin (m i)), Function.Surjective (fun k : K => k.1 i j)

theorem occurrenceFull_curry_map_iff
    (K : Subgroup ((o : Σ i, Fin (m i)) → (F o.1).Carrier)) :
    OccurrenceFull F m (K.map (curryOccurrences F m).toMonoidHom) ↔
      IndexedFull (fun o : Σ i, Fin (m i) => F o.1) K := by
  constructor
  · intro h ⟨i,j⟩ u
    obtain ⟨x,hx⟩ := h i j u
    obtain ⟨y,hy,he⟩ := Subgroup.mem_map.mp x.2
    refine ⟨⟨y,hy⟩,?_⟩
    exact (congrFun (congrFun he i) j).trans hx
  · intro h i j u
    obtain ⟨x,hx⟩ := h ⟨i,j⟩ u
    exact ⟨⟨curryOccurrences F m x.1,Subgroup.mem_map.mpr ⟨x.1,x.2,rfl⟩⟩,hx⟩

theorem occurrenceFull_map_iff (H : Subgroup (Product (occurrenceWord F m e))) :
    OccurrenceFull F m (H.map (occurrenceEquiv F m e).toMonoidHom) ↔
      Full (occurrenceWord F m e) H := by
  have he : H.map (occurrenceEquiv F m e).toMonoidHom =
      (H.map (reindexedWordEquiv (occurrenceWord F m e)
        (fun o : Σ i, Fin (m i) => F o.1) (occurrenceEnumeration F m e)
        (occurrenceWord_get F m e)).toMonoidHom).map
          (curryOccurrences F m).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [he, occurrenceFull_curry_map_iff]
  exact indexedFull_map_iff _ _ _ _ H

/-- Predicate transport uses the exact original inverse image. It does
not require the predicate or an associated weight to factor by occurrence. -/
def occurrenceFamilyEquiv
    (P : Subgroup (Product (occurrenceWord F m e)) → Prop) :
    {H : Family (occurrenceWord F m e) // P H.1} ≃
      {K : Subgroup (OccurrenceProduct F m) // OccurrenceFull F m K ∧
        P (K.comap (occurrenceEquiv F m e).toMonoidHom)} where
  toFun H :=
    ⟨H.1.1.map (occurrenceEquiv F m e).toMonoidHom,
      (occurrenceFull_map_iff F m e H.1.1).mpr H.1.2,by
        rw [Subgroup.comap_map_eq_self_of_injective
          (f := (occurrenceEquiv F m e).toMonoidHom) (occurrenceEquiv F m e).injective]
        exact H.2⟩
  invFun K :=
    ⟨⟨K.1.comap (occurrenceEquiv F m e).toMonoidHom,by
      apply (occurrenceFull_map_iff F m e _).mp
      rw [Subgroup.map_comap_eq_self_of_surjective
        (f := (occurrenceEquiv F m e).toMonoidHom) (occurrenceEquiv F m e).surjective]
      exact K.2.1⟩,K.2.2⟩
  left_inv H := by
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective
      (occurrenceEquiv F m e).injective H.1.1
  right_inv K := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self_of_surjective
      (occurrenceEquiv F m e).surjective K.1

theorem occurrenceFamilyEquiv_reconstruct
    (P : Subgroup (Product (occurrenceWord F m e)) → Prop)
    (H : {H : Family (occurrenceWord F m e) // P H.1}) :
    (occurrenceFamilyEquiv F m e P H).1.comap
        (occurrenceEquiv F m e).toMonoidHom = H.1.1 :=
  Subgroup.comap_map_eq_self_of_injective (occurrenceEquiv F m e).injective H.1.1

end SymmetricSubgroupAsymptotics.BinaryCarrierOccurrenceWord
