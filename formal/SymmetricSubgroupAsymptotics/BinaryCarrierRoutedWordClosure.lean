import SymmetricSubgroupAsymptotics.BinaryDegreeEightPhysicalAnalyticClosure

/-!
# Routed exact-axis words enter the carrier mixture

The local finite classifiers produce source groups only up to explicit group
equivalence.  This file changes all source coordinates simultaneously by
those equivalences, proves that coordinate fullness and every exact normal
axis are preserved, and then applies the heterogeneous carrier-word theorem.
The counted source object remains the original full subgroup with its fixed
axis predicate; the route, quotient maps, and point relabellings are not
additional markings.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRoutedWordClosure

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryDegreeEightPhysicalAnalyticClosure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (A : ι → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
  (N : ∀ i, Subgroup (A i))
  (R : ∀ i, AxisSlot (A i) (N i))

abbrev slots (i : ι) : Slot.{0,0,0} := (R i).slot

/-- Change every original source coordinate by its routed equivalence. -/
def sourceProductEquiv : (∀ i, A i) ≃* (∀ i, (slots A N R i).Source) :=
  MulEquiv.piCongrRight (fun i => (R i).sourceEquiv)

@[simp] theorem sourceProductEquiv_apply (x : ∀ i, A i) (i : ι) :
    sourceProductEquiv A N R x i = (R i).sourceEquiv (x i) := rfl

@[simp] theorem sourceProductEquiv_toMonoidHom_apply
    (x : ∀ i, A i) (i : ι) :
    (sourceProductEquiv A N R).toMonoidHom x i =
      (R i).sourceEquiv.toMonoidHom (x i) := rfl

/-- A product equivalence transports the embedded coordinate axis by the
corresponding local equivalence. -/
theorem carrierAxis_map_sourceProductEquiv
    (H : Subgroup (∀ i, A i)) (i : ι) :
    carrierAxis (H.map (sourceProductEquiv A N R).toMonoidHom) i =
      (carrierAxis H i).map (R i).sourceEquiv.toMonoidHom := by
  ext x
  constructor
  · intro hx
    change MonoidHom.mulSingle (fun i => (slots A N R i).Source) i x ∈
      H.map (sourceProductEquiv A N R).toMonoidHom at hx
    obtain ⟨y,hy,he⟩ := Subgroup.mem_map.mp hx
    have hoff : ∀ j, j ≠ i → y j = 1 := by
      intro j hji
      have hj := congrFun he j
      change (R j).sourceEquiv (y j) = _ at hj
      rw [MonoidHom.mulSingle_apply,Pi.mulSingle_eq_of_ne hji] at hj
      exact (R j).sourceEquiv.injective (hj.trans (R j).sourceEquiv.map_one.symm)
    have hyaxis : y i ∈ carrierAxis H i := by
      change MonoidHom.mulSingle A i (y i) ∈ H
      convert hy using 1
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · rw [MonoidHom.mulSingle_apply,Pi.mulSingle_eq_of_ne hji,hoff j hji]
    refine Subgroup.mem_map.mpr ⟨y i,hyaxis,?_⟩
    have hi := congrFun he i
    change (R i).sourceEquiv (y i) = _ at hi
    simpa using hi
  · intro hx
    obtain ⟨y,hy,he⟩ := Subgroup.mem_map.mp hx
    change MonoidHom.mulSingle (fun i => (slots A N R i).Source) i x ∈
      H.map (sourceProductEquiv A N R).toMonoidHom
    refine Subgroup.mem_map.mpr
      ⟨MonoidHom.mulSingle A i y,hy,?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simpa only [sourceProductEquiv_toMonoidHom_apply,
        MonoidHom.mulSingle_apply,Pi.mulSingle_eq_same] using he
    · simp [sourceProductEquiv,slots,hji]

/-- The original unmarked fixed-axis stratum. -/
abbrev ExactAxisFamily :=
  {H : Subgroup (∀ i, A i) //
    CarrierProductFull H ∧ ∀ i, carrierAxis H i = N i}

/-- Simultaneous coordinate transport turns an original exact-axis subgroup
into the source record expected by the heterogeneous carrier word. -/
def routedSource : ExactAxisFamily A N →
    CarrierTransportSource (alphas (slots A N R)) := fun H => by
  refine ⟨H.1.map (sourceProductEquiv A N R).toMonoidHom,?_,?_⟩
  · intro i u
    obtain ⟨h,hh⟩ := H.2.1 i ((R i).sourceEquiv.symm u)
    refine ⟨⟨sourceProductEquiv A N R h.1,
      Subgroup.mem_map.mpr ⟨h.1,h.2,rfl⟩⟩,?_⟩
    change (R i).sourceEquiv (h.1 i) = u
    rw [hh]
    exact (R i).sourceEquiv.apply_symm_apply u
  · intro i
    rw [carrierAxis_map_sourceProductEquiv A N R H.1 i,H.2.2 i]
    exact (R i).kernel

/-- The coordinate change is reversible, so it adds no multiplicity. -/
theorem routedSource_injective : Function.Injective (routedSource A N R) := by
  intro H K h
  apply Subtype.ext
  apply Subgroup.map_injective
    (f := (sourceProductEquiv A N R).toMonoidHom)
    (sourceProductEquiv A N R).injective
  exact congrArg Subtype.val h

/-- Any finite routed exact-axis word with a displayed noncritical cell is
absorbed by the one completed-mixture parameter bin determined by its slots. -/
theorem exact_axis_word_card_le_mixture
    (hnoncritical : ∃ c : Σ i, cells (slots A N R) i, ∃ t,
      colors (slots A N R) c = .inr t) :
    Nat.card (ExactAxisFamily A N) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter (cells (slots A N R)) (colors (slots A N R)))) := by
  exact (Nat.card_le_card_of_injective _
    (routedSource_injective A N R)).trans
      (slot_source_card_le_mixture (slots A N R) hnoncritical)

/-- It is enough to retain a positive-support witness on one routed slot. -/
theorem exact_axis_word_card_le_mixture_of_supported
    (i : ι) (hi : (R i).HasNoncritical) :
    Nat.card (ExactAxisFamily A N) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family
        (parameter (cells (slots A N R)) (colors (slots A N R)))) := by
  apply exact_axis_word_card_le_mixture A N R
  obtain ⟨c,t,hc⟩ := hi
  exact ⟨⟨i,c⟩,t,hc⟩

/-! ## Finite local-to-word choice -/

/-- If every local axis is either direct or routed, then either some direct
owner is present or all routed slots can be chosen simultaneously. -/
theorem direct_or_all_slots
    (D : ι → Prop)
    (h : ∀ i, D i ∨ Nonempty (AxisSlot (A i) (N i))) :
    (∃ i, D i) ∨ Nonempty (∀ i, AxisSlot (A i) (N i)) := by
  classical
  by_cases hd : ∃ i, D i
  · exact Or.inl hd
  · right
    exact ⟨fun i => Classical.choice ((h i).resolve_left
      (fun hi => hd ⟨i,hi⟩))⟩

/-- The same choice lemma with the mixture positivity witness retained at
every carrier coordinate. -/
theorem direct_or_all_supported_slots
    (D : ι → Prop)
    (h : ∀ i, D i ∨
      Nonempty {S : AxisSlot (A i) (N i) // S.HasNoncritical}) :
    (∃ i, D i) ∨
      Nonempty (∀ i, {S : AxisSlot (A i) (N i) // S.HasNoncritical}) := by
  classical
  by_cases hd : ∃ i, D i
  · exact Or.inl hd
  · right
    exact ⟨fun i => Classical.choice ((h i).resolve_left
      (fun hi => hd ⟨i,hi⟩))⟩

/-- With the complete support classification on every routed coordinate,
the all-carrier branch either has a positive-support slot or is pure E8 in
every coordinate. -/
theorem direct_or_supported_word_or_pureE8
    (D : ι → Prop)
    (h : ∀ i, D i ∨ Nonempty
      {S : AxisSlot (A i) (N i) // S.HasNoncritical ∨ S.IsPureE8}) :
    (∃ i, D i) ∨
      ∃ R : ∀ i, AxisSlot (A i) (N i),
        (∃ i, (R i).HasNoncritical) ∨ ∀ i, (R i).IsPureE8 := by
  classical
  by_cases hd : ∃ i, D i
  · exact Or.inl hd
  · right
    let C : ∀ i, {S : AxisSlot (A i) (N i) //
        S.HasNoncritical ∨ S.IsPureE8} := fun i =>
      Classical.choice ((h i).resolve_left (fun hi => hd ⟨i,hi⟩))
    let R : ∀ i, AxisSlot (A i) (N i) := fun i => (C i).1
    refine ⟨R,?_⟩
    by_cases hs : ∃ i, (R i).HasNoncritical
    · exact Or.inl hs
    · exact Or.inr (fun i => (C i).2.resolve_left
        (fun hi => hs ⟨i,hi⟩))

end SymmetricSubgroupAsymptotics.BinaryCarrierRoutedWordClosure
