import SymmetricSubgroupAsymptotics.BinaryCarrierProfileTransport

/-!
# Canonical parameter profiles from finite carrier cells

A simultaneous carrier word supplies finitely many displayed cells, each
labelled by one action in the completed mixture alphabet.  The fibre sizes of
that labelling canonically determine the critical profile, the C4
multiplicity, the carrier scale, and the exact parameter-bin index.  This
removes all hand-selected multiplicity bookkeeping from the global transport.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCellProfile

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryCarrierParameterProfiles

variable {ι : Type*} [Fintype ι]
  (κ : ι → Type*) [∀ i, Fintype (κ i)]

abbrev Cell := Σ i, κ i
abbrev Kind := BinaryCarrierProfileTransport.MixtureKind

variable (color : Cell κ → Kind)

def fiber (g : Kind) := {c : Cell κ // color c = g}

instance fiberFintype (g : Kind) : Fintype (fiber κ color g) := by
  classical
  exact Fintype.ofInjective (fun c : fiber κ color g => c.1)
    Subtype.val_injective

/-- The exact number of displayed cells of each original-action colour. -/
def multiplicity (g : Kind) : ℕ := Fintype.card (fiber κ color g)

/-- Enumerate every colour fibre and then forget the fibre proof. -/
def occurrenceToCell :
    (Σ g, Fin (multiplicity κ color g)) ≃ Cell κ where
  toFun o := ((Fintype.equivFin (fiber κ color o.1)).symm o.2).1
  invFun c :=
    ⟨color c,Fintype.equivFin (fiber κ color (color c)) ⟨c,rfl⟩⟩
  left_inv := fun o =>
    ((Equiv.sigmaCongrRight
      (fun g => (Fintype.equivFin (fiber κ color g)).symm)).trans
        (Equiv.sigmaFiberEquiv color)).left_inv o
  right_inv := fun c =>
    ((Equiv.sigmaCongrRight
      (fun g => (Fintype.equivFin (fiber κ color g)).symm)).trans
        (Equiv.sigmaFiberEquiv color)).right_inv c

/-- The canonical assignment used by `assignedProfileDisplay`. -/
def cellToOccurrence :
    Cell κ ≃ (Σ g, Fin (multiplicity κ color g)) :=
  (occurrenceToCell κ color).symm

theorem occurrenceToCell_color (o : Σ g, Fin (multiplicity κ color g)) :
    color (occurrenceToCell κ color o) = o.1 := by
  rcases o with ⟨g,j⟩
  exact ((Fintype.equivFin (fiber κ color g)).symm j).2

@[simp] theorem cellToOccurrence_color (c : Cell κ) :
    (cellToOccurrence κ color c).1 = color c := by
  let o := cellToOccurrence κ color c
  have ho : occurrenceToCell κ color o = c :=
    (occurrenceToCell κ color).apply_symm_apply c
  calc
    o.1 = color (occurrenceToCell κ color o) :=
      (occurrenceToCell_color κ color o).symm
    _ = color c := congrArg color ho

/-- Critical multiplicities are read directly from the four critical cell
fibres. -/
def critical : CriticalProfile where
  c2 := multiplicity κ color (.inl .c2)
  v4 := multiplicity κ color (.inl .v4)
  d8 := multiplicity κ color (.inl .d8)
  e8 := multiplicity κ color (.inl .e8)

/-- Original noncritical multiplicities, including the regular C4 colour. -/
def noncritical : BinaryCarrierOriginalCyclicFourHall.Target → ℕ
  | none => multiplicity κ color (.inr none)
  | some t => multiplicity κ color (.inr (some t))

def criticalRank : ℕ := (critical κ color).rank
def cyclicMultiplicity : ℕ := noncritical κ color none
def carrierScale : ℕ :=
  BinaryCarrierOriginalActions.scale (fun t => noncritical κ color (some t))

theorem critical_mem :
    critical κ color ∈ criticalProfiles (criticalRank κ color) := by
  simp only [criticalRank,mem_criticalProfiles]

theorem noncritical_parameters :
    noncritical κ color none = cyclicMultiplicity κ color ∧
      BinaryCarrierOriginalActions.scale
        (fun t => noncritical κ color (some t)) = carrierScale κ color :=
  ⟨rfl,rfl⟩

/-- The exact completed-mixture parameter index determined by the cells. -/
def index : ProfileIndex (criticalRank κ color)
    (cyclicMultiplicity κ color) (carrierScale κ color) :=
  ⟨⟨critical κ color,critical_mem κ color⟩,
    ⟨noncritical κ color,
      (mem_profilesAtParameters (cyclicMultiplicity κ color)
        (carrierScale κ color) (noncritical κ color)).mpr
          (noncritical_parameters κ color)⟩⟩

/-- The index recovers every cell-fibre multiplicity literally. -/
theorem indexed_multiplicity :
    profileMultiplicity (criticalRank κ color)
      (cyclicMultiplicity κ color) (carrierScale κ color) (index κ color) =
        multiplicity κ color := by
  funext g
  rcases g with g|t
  · rcases g with _|_|_|_ <;> rfl
  · rcases t with _|t <;> rfl

/-- Reindex the canonical cell occurrences directly into the completed-profile
multiplicity.  Keeping this equality at the occurrence level avoids casting an
entire dependent `ProfileDisplay`. -/
def cellToProfileOccurrence :
    Cell κ ≃
      ( Σ g, Fin (profileMultiplicity (criticalRank κ color)
        (cyclicMultiplicity κ color) (carrierScale κ color)
        (index κ color) g)) :=
  (cellToOccurrence κ color).trans
    (Equiv.sigmaCongrRight (fun g => Equiv.cast
      (congrArg Fin (congrFun (indexed_multiplicity κ color) g).symm)))

@[simp] theorem cellToProfileOccurrence_color (c : Cell κ) :
    (cellToProfileOccurrence κ color c).1 = color c := rfl

/-- The canonical cell enumeration supplies the exact completed-profile
display, already expressed on the literal original-action groups. -/
def display :
    ProfileDisplay
      (V := fun i j => mixtureAction (color ⟨i,j⟩))
      mixtureAction
      (profileMultiplicity (criticalRank κ color)
        (cyclicMultiplicity κ color) (carrierScale κ color)
        (index κ color)) :=
  assignedProfileDisplay mixtureAction
    (profileMultiplicity (criticalRank κ color)
      (cyclicMultiplicity κ color) (carrierScale κ color)
      (index κ color))
    (cellToProfileOccurrence κ color)

/-- The direct display already uses every cell's original action. -/
def originalCellEquiv (i : ι) (j : κ i) :
    mixtureAction (color ⟨i,j⟩) ≃* mixtureAction (color ⟨i,j⟩) :=
  MulEquiv.refl _

/-- The exact profile display on the literal, originally coloured carrier
cells.  No relabelling datum remains in the hypotheses of a global carrier
word: it is derived canonically from the finite colour fibres. -/
def originalColorDisplay :
    ProfileDisplay
      (V := fun i j => mixtureAction (color ⟨i,j⟩))
      mixtureAction
      (profileMultiplicity (criticalRank κ color)
        (cyclicMultiplicity κ color) (carrierScale κ color) (index κ color)) :=
  display κ color

theorem multiplicity_pos_of_cell {g : Kind} {c : Cell κ}
    (hc : color c = g) : 0 < multiplicity κ color g := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨c,hc⟩⟩

/-- One noncritical displayed cell makes the resulting mixture support
positive.  This is the only guard needed to enter the completed union. -/
theorem support_pos_of_noncritical
    (h : ∃ c : Cell κ, ∃ t, color c = .inr t) :
    0 < 2*cyclicMultiplicity κ color + 4*carrierScale κ color := by
  obtain ⟨c,t,hc⟩ := h
  cases t with
  | none =>
      have hm := multiplicity_pos_of_cell κ color hc
      change 0 < 2*multiplicity κ color (.inr none) + 4*carrierScale κ color
      omega
  | some t =>
      have hm := multiplicity_pos_of_cell κ color hc
      have hle := BinaryCarrierSmallSupportPhysical.carrierMultiplicity_le_scale
        (fun s => noncritical κ color (some s)) t
      change 0 < 2*cyclicMultiplicity κ color + 4*carrierScale κ color
      change multiplicity κ color (.inr (some t)) ≤ carrierScale κ color at hle
      omega

end SymmetricSubgroupAsymptotics.BinaryCarrierCellProfile
