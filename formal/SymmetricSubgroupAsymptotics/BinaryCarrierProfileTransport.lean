import SymmetricSubgroupAsymptotics.BinaryTransport
import SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierMixtureCompletion

/-!
# Simultaneous carrier transport into a physical mixture profile

`BinaryTransport` reconstructs an original full subgroup after replacing all
of its coordinates by arbitrary proper subdirect carriers.  This file supplies
the missing packaging layer: once the displayed carrier cells are identified
with the occurrences of one original-action orbit profile, the simultaneous
transport is an injection into that full profile and hence into the completed
carrier-mixture parameter bin.

The display hypothesis contains no counting estimate.  It records only a
group equivalence between the literal displayed cells and the literal profile
product, together with the fact that fullness on every displayed cell becomes
fullness on every profile occurrence.  In particular the carrier at one
source coordinate may remain nonabelian and proper subdirect.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierProfileTransport

open SymmetricSubgroupAsymptotics

variable {ι γ : Type*} [Fintype γ]
  {U P Q : ι → Type*}
  [∀ i, Group (U i)] [∀ i, Group (P i)] [∀ i, Group (Q i)]
  {κ : ι → Type*} {V : ∀ i, κ i → Type*} [∀ i j, Group (V i j)]
  {Ω : γ → Type*} (A : ∀ g, Subgroup (Equiv.Perm (Ω g))) (m : γ → ℕ)

/-- A literal identification of every displayed carrier cell with one
occurrence of a target orbit profile.  The second field is the only required
compatibility: coordinate fullness must survive the identification. -/
structure ProfileDisplay where
  productEquiv : (∀ i j, V i j) ≃*
    OrbitProfileProductGroup m A
  full_map : ∀ H : Subgroup (∀ i j, V i j),
    CarrierDisplayedFull H →
      OrbitProfileProductFull m A (H.map productEquiv.toMonoidHom)

/-- A fixed profile display acts directly on an arbitrary full subgroup of
the literal displayed ambient.  This is the source-independent part of
`productTransport`: the quotient maps which produced the ambient subgroup
are no longer present. -/
def ProfileDisplay.productTarget
    (D : ProfileDisplay (V := V) A m) :
    CarrierTransportTarget (V := V) →
      {K : Subgroup (OrbitProfileProductGroup m A) //
        OrbitProfileProductFull m A K} := fun H =>
  ⟨H.1.map D.productEquiv.toMonoidHom, D.full_map H.1 H.2⟩

/-- A fixed display loses no literal ambient subgroup.  Proper subdirect
relations inside any displayed carrier are retained because the only map is
the product equivalence belonging to the display. -/
theorem ProfileDisplay.productTarget_injective
    (D : ProfileDisplay (V := V) A m) :
    Function.Injective D.productTarget := by
  intro H K h
  apply Subtype.ext
  apply Subgroup.map_injective (f := D.productEquiv.toMonoidHom)
    D.productEquiv.injective
  exact congrArg Subtype.val h

variable [∀ g, Fintype (Ω g)]

/-- Apply the faithful independent orbit action after a fixed display. -/
def ProfileDisplay.modelTarget
    (D : ProfileDisplay (V := V) A m) :
    CarrierTransportTarget (V := V) →
      {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) //
        OrbitProfileFull A 1 K} := fun H =>
  orbitProfileProductFullEquiv m A
    (ProfileDisplay.productTarget A m D H)

theorem ProfileDisplay.modelTarget_injective
    (D : ProfileDisplay (V := V) A m) :
    Function.Injective D.modelTarget :=
  (orbitProfileProductFullEquiv m A).injective.comp
    (ProfileDisplay.productTarget_injective A m D)

section ChangeDisplayedGroups

variable {W : ∀ i, κ i → Type*} [∀ i j, Group (W i j)]

/-- Change each displayed cell by a fixed group equivalence. -/
def displayedProductEquiv
    (L : ∀ i j, W i j ≃* V i j) :
    (∀ i j, W i j) ≃* (∀ i j, V i j) :=
  MulEquiv.piCongrRight (fun i => MulEquiv.piCongrRight (L i))

/-- Pull a profile display back through independent equivalences on all
displayed cells.  This is useful when a canonical fibre enumeration changes
only the dependent types of literal original-action coordinates. -/
def ProfileDisplay.pullback
    (D : ProfileDisplay (V := V) A m)
    (L : ∀ i j, W i j ≃* V i j) :
    ProfileDisplay (V := W) A m where
  productEquiv := (displayedProductEquiv L).trans D.productEquiv
  full_map := by
    intro H hH
    have hfull : CarrierDisplayedFull
        (H.map (displayedProductEquiv L).toMonoidHom) := by
      intro i j v
      obtain ⟨h,hh⟩ := hH i j ((L i j).symm v)
      refine ⟨⟨displayedProductEquiv L h.1,
        Subgroup.mem_map.mpr ⟨h.1,h.2,rfl⟩⟩,?_⟩
      change L i j (h.1 i j) = v
      rw [hh]
      exact (L i j).apply_symm_apply v
    have htarget := D.full_map
      (H.map (displayedProductEquiv L).toMonoidHom) hfull
    simpa only [Subgroup.map_map] using htarget

end ChangeDisplayedGroups

section AssignedCells

variable [Fintype ι] [∀ i, Fintype (κ i)]

/-- Reindex a dependent product along a bijection. -/
def piReindex {δ ε : Type*} (G : ε → Type*) [∀ e, Group (G e)]
    (e : δ ≃ ε) : ((y : ε) → G y) ≃* ((x : δ) → G (e x)) :=
  { (Equiv.piCongrLeft G e).symm with
    map_mul' := fun _ _ => rfl }

@[simp] theorem piReindex_symm_apply {δ ε : Type*}
    (G : ε → Type*) [∀ e, Group (G e)] (e : δ ≃ ε)
    (f : (x : δ) → G (e x)) (x : δ) :
    (piReindex G e).symm f (e x) = f x :=
  Equiv.piCongrLeft_apply_apply G e f x

/-- Curry the displayed cells without changing any local group. -/
def displayedCurry
    (e : (Σ i, κ i) ≃ (Σ g, Fin (m g))) :
    (∀ i j, A (e ⟨i,j⟩).1) ≃*
      ((c : Σ i, κ i) → A (e c).1) :=
  { (Equiv.piCurry (fun i (j : κ i) => A (e ⟨i,j⟩).1)).symm with
    map_mul' := fun _ _ => rfl }

/-- Curry the target orbit occurrences. -/
def profileCurry :
    OrbitProfileProductGroup m A ≃*
      ((o : Σ g, Fin (m g)) → A o.1) :=
  { (Equiv.piCurry (fun g (_ : Fin (m g)) => A g)).symm with
    map_mul' := fun _ _ => rfl }

/-- A bijection from displayed cells to target occurrences induces the
literal group equivalence required by `ProfileDisplay`. -/
def assignedProductEquiv
    (e : (Σ i, κ i) ≃ (Σ g, Fin (m g))) :
    (∀ i j, A (e ⟨i,j⟩).1) ≃* OrbitProfileProductGroup m A :=
  ((displayedCurry A m e).trans
    (piReindex (fun o : Σ g, Fin (m g) => A o.1) e).symm).trans
      (profileCurry A m).symm

@[simp] theorem assignedProductEquiv_apply
    (e : (Σ i, κ i) ≃ (Σ g, Fin (m g)))
    (f : ∀ i j, A (e ⟨i,j⟩).1) (c : Σ i, κ i) :
    assignedProductEquiv A m e f (e c).1 (e c).2 = f c.1 c.2 := by
  have h := piReindex_symm_apply (fun o : Σ g, Fin (m g) => A o.1) e
    (displayedCurry A m e f) c
  simpa only [assignedProductEquiv,profileCurry,displayedCurry,
    MulEquiv.trans_apply] using h

/-- Cellwise fullness becomes target-profile fullness solely by reindexing.
This is the fusion-natural constructor used by a simultaneous carrier word:
the assignment may interleave cells from different proper carriers and may
send several cells to repeated occurrences of the same target colour. -/
def assignedProfileDisplay
    (e : (Σ i, κ i) ≃ (Σ g, Fin (m g))) :
    ProfileDisplay (V := fun i j => A (e ⟨i,j⟩).1) A m where
  productEquiv := assignedProductEquiv A m e
  full_map := by
    intro H hH g j u
    let c : Σ i, κ i := e.symm ⟨g,j⟩
    have hc : e c = ⟨g,j⟩ := e.apply_symm_apply ⟨g,j⟩
    have hgc : g = (e c).1 := (congrArg Sigma.fst hc).symm
    let v : A (e c).1 := hgc ▸ u
    obtain ⟨h,hh⟩ := hH c.1 c.2 v
    refine ⟨⟨assignedProductEquiv A m e h.1,
      Subgroup.mem_map.mpr ⟨h.1,h.2,rfl⟩⟩,?_⟩
    let z := profileCurry A m (assignedProductEquiv A m e h.1)
    have hz : z (e c) = v := by
      exact (assignedProductEquiv_apply A m e h.1 c).trans hh
    have hleft : HEq (z (e c)) (z ⟨g,j⟩) := by
      let pack : (o : Σ g, Fin (m g)) →
          (Σ o : (Σ g, Fin (m g)), A o.1) :=
        fun o => ⟨o,z o⟩
      exact (Sigma.mk.inj_iff.mp (congrArg pack hc)).2
    have hright : HEq v u := by
      exact rec_heq_of_heq (C := fun x => A x) hgc (HEq.rfl)
    change z ⟨g,j⟩ = u
    exact eq_of_heq (hleft.symm.trans ((heq_of_eq hz).trans hright))

end AssignedCells

variable (D : ProfileDisplay (V := V) A m)
  (C : ∀ i, Subgroup (∀ j, V i j))
  (hC : ∀ i, CarrierProductFull (C i))
  (α : ∀ i, U i →* Q i) (β : ∀ i, C i →* Q i)
  (hα : ∀ i, Function.Surjective (α i))
  (hβ : ∀ i, Function.Surjective (β i))

/-- Simultaneously replace all source coordinates and then read the displayed
cells as one full subgroup of the target orbit-product. -/
def productTransport [DecidableEq ι] :
    CarrierTransportSource α →
      {K : Subgroup (OrbitProfileProductGroup m A) //
        OrbitProfileProductFull m A K} := fun H =>
  let J := carrierTransportRecords C hC α β hα hβ H
  ⟨J.1.map D.productEquiv.toMonoidHom, D.full_map J.1 J.2⟩

/-- Reversibility of the carrier construction and injectivity of the display
equivalence recover the original subgroup from the target profile. -/
theorem productTransport_injective [Finite ι] [DecidableEq ι] :
    Function.Injective (productTransport A m D C hC α β hα hβ) := by
  intro H K h
  apply carrierTransportRecords_injective C hC α β hα hβ
  apply Subtype.ext
  exact Subgroup.map_injective (f := D.productEquiv.toMonoidHom)
    D.productEquiv.injective (congrArg Subtype.val h)

variable [∀ g, Fintype (Ω g)]

/-- Apply the faithful independent action of the target profile.  This keeps
the complete transported relation and produces the exact model fibre used by
physical orbit-profile assembly. -/
def modelTransport [DecidableEq ι] :
    CarrierTransportSource α →
      {K : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) //
        OrbitProfileFull A 1 K} := fun H =>
  orbitProfileProductFullEquiv m A
    (productTransport A m D C hC α β hα hβ H)

theorem modelTransport_injective [Finite ι] [DecidableEq ι] :
    Function.Injective (modelTransport A m D C hC α β hα hβ) :=
  (orbitProfileProductFullEquiv m A).injective.comp
    (productTransport_injective A m D C hC α β hα hβ)

section Mixture

open BinaryCarrierParameterProfiles

abbrev MixtureKind := CriticalActionKind ⊕
  BinaryCarrierOriginalCyclicFourHall.Target

abbrev mixturePoints : MixtureKind → Type :=
  BinaryCarrierMixedProfile.points
    BinaryCarrierOriginalCyclicFourHall.points

abbrev mixtureAction : (g : MixtureKind) →
    Subgroup (Equiv.Perm (mixturePoints g)) :=
  BinaryCarrierMixedProfile.action
    BinaryCarrierOriginalCyclicFourHall.points
    BinaryCarrierOriginalCyclicFourHall.action

variable {R a T : ℕ} (s : ProfileIndex R a T)
  (Dmix : ProfileDisplay (V := V) mixtureAction
    (profileMultiplicity R a T s))

/-- The source-independent fixed-chart map from the literal displayed
ambient subgroup to the physical labelled parameter bin.  This is the map
whose injectivity is needed when the source quotient and its normal axes vary
inside one block-decoration fibre. -/
def ProfileDisplay.physicalTarget :
    CarrierTransportTarget (V := V) →
      PhysicalFamily R a T (Fin (2*(R+2*a+4*T))) := fun H => by
  let M := ProfileDisplay.modelTarget (Ω := mixturePoints)
    mixtureAction (profileMultiplicity R a T s) Dmix H
  let e := orbitProfileFinLabels mixturePoints (profileMultiplicity R a T s)
    (2*(R+2*a+4*T)) (physicalDegree R a T s)
  refine ⟨relabelSubgroup e M.1, s, e, M.1, ?_, rfl⟩
  exact M.2

/-- Faithfulness of the display equivalence, orbit action, and final
relabelling makes the fixed-chart physical realization injective. -/
theorem ProfileDisplay.physicalTarget_injective :
    Function.Injective (ProfileDisplay.physicalTarget s Dmix) := by
  intro H K h
  apply ProfileDisplay.modelTarget_injective (Ω := mixturePoints)
    mixtureAction (profileMultiplicity R a T s) Dmix
  apply Subtype.ext
  apply (relabelSubgroup
    (orbitProfileFinLabels mixturePoints (profileMultiplicity R a T s)
      (2*(R+2*a+4*T)) (physicalDegree R a T s))).injective
  exact congrArg Subtype.val h

/-- The exact target model, relabelled onto its physical point set, is a
member of the specified original-action parameter bin. -/
def physicalTransport [DecidableEq ι] :
    CarrierTransportSource α →
      PhysicalFamily R a T (Fin (2*(R+2*a+4*T))) := fun H => by
  let M := modelTransport mixtureAction (profileMultiplicity R a T s)
    Dmix C hC α β hα hβ H
  let e := orbitProfileFinLabels mixturePoints (profileMultiplicity R a T s)
    (2*(R+2*a+4*T)) (physicalDegree R a T s)
  refine ⟨relabelSubgroup e M.1, s, e, M.1, ?_, rfl⟩
  exact M.2

/-- `physicalTransport` factors through the literal simultaneous ambient
subgroup and the source-independent fixed-chart realization above. -/
theorem physicalTransport_eq_physicalTarget [DecidableEq ι]
    (H : CarrierTransportSource α) :
    physicalTransport C hC α β hα hβ s Dmix H =
      ProfileDisplay.physicalTarget s Dmix
        (carrierTransportRecords C hC α β hα hβ H) := by
  rfl

theorem physicalTransport_injective [Finite ι] [DecidableEq ι] :
    Function.Injective (physicalTransport C hC α β hα hβ s Dmix) := by
  intro H K h
  apply modelTransport_injective mixtureAction
    (profileMultiplicity R a T s) Dmix C hC α β hα hβ
  apply Subtype.ext
  apply (relabelSubgroup
    (orbitProfileFinLabels mixturePoints (profileMultiplicity R a T s)
      (2*(R+2*a+4*T)) (physicalDegree R a T s))).injective
  exact congrArg Subtype.val h

/-- Positive noncritical support installs the fixed target profile in the
completed all-parameter mixture family. -/
def mixtureTransport (hsupport : 0 < 2*a+4*T) [DecidableEq ι] :
    CarrierTransportSource α →
      BinaryCarrierMixtureCompletion.Family (R+2*a+4*T) := fun H => by
  let b : BinaryCarrierParameterUnion.bins (R+2*a+4*T) (fun _ _ => True) :=
    ⟨(a,T),by
      rw [BinaryCarrierParameterUnion.mem_bins]
      exact ⟨hsupport,by omega,True.intro⟩⟩
  let K := physicalTransport C hC α β hα hβ s Dmix H
  have hR : R+2*a+4*T-(2*a+4*T)=R := by omega
  refine ⟨K.1,b,?_,?_⟩
  · refine ⟨K.1,?_⟩
    rw [hR]
    exact K.2
  · rfl

theorem mixtureTransport_injective (hsupport : 0 < 2*a+4*T)
    [Finite ι] [DecidableEq ι] :
    Function.Injective
      (mixtureTransport (C := C) (hC := hC) (α := α) (β := β)
        (hα := hα) (hβ := hβ) (s := s) (Dmix := Dmix) hsupport) := by
  intro H K h
  apply physicalTransport_injective C hC α β hα hβ s Dmix
  apply Subtype.ext
  exact congrArg
    (fun J : BinaryCarrierMixtureCompletion.Family (R+2*a+4*T) => J.1) h

variable [∀ i, Finite (U i)] [∀ i, Finite (κ i)]
  [∀ i j, Finite (V i j)]

private instance physicalFamilyFinite :
    Finite (PhysicalFamily R a T (Fin (2*(R+2*a+4*T)))) := by
  unfold PhysicalFamily AssembledOrbitProfilesOn
  infer_instance

include C hC β hα hβ s Dmix

/-- A fixed simultaneous all-carrier source family is bounded by the exact
physical parameter bin, with no orbit, chart, or axis marking on the target. -/
theorem source_card_le_physical [Finite ι] [DecidableEq ι] :
    Nat.card (CarrierTransportSource α) ≤
      Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T)))) :=
  Nat.card_le_card_of_injective _
    (physicalTransport_injective C hC α β hα hβ s Dmix)

/-- The same fixed decorated source injects into the already completed
negligible carrier-mixture family whenever its noncritical support is
positive. -/
theorem source_card_le_mixture (hsupport : 0 < 2*a+4*T)
    [Finite ι] [DecidableEq ι] :
    Nat.card (CarrierTransportSource α) ≤
      Nat.card (BinaryCarrierMixtureCompletion.Family (R+2*a+4*T)) :=
  Nat.card_le_card_of_injective _
    (mixtureTransport_injective (C := C) (hC := hC) (α := α) (β := β)
      (hα := hα) (hβ := hβ) (s := s) (Dmix := Dmix) hsupport)

end Mixture

end SymmetricSubgroupAsymptotics.BinaryCarrierProfileTransport
