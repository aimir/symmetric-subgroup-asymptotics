import SymmetricSubgroupAsymptotics.OrbitProfileWeightedAssembly
import Mathlib.Data.Finset.Image

/-!
# Actual two-point orbit marks

A pair is an actual orbit subset of the original labelled point set. Two
pairs have the same binary character precisely when the elements of the
original subgroup fixing either pair pointwise are the same. This definition
does not choose an orientation or a two-point chart. The duplicate mark is
an unordered two-element set of these actual orbits.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationPairOrbitMarks

variable {X Y : Type*}

def IsPairOrbit (H : Subgroup (Equiv.Perm X)) (s : Set X) : Prop :=
  (∃ x, s = MulAction.orbit H x) ∧ Nat.card s = 2

abbrev PairOrbit (H : Subgroup (Equiv.Perm X)) := {s : Set X // IsPairOrbit H s}

def Fixes (g : Equiv.Perm X) (s : Set X) : Prop := ∀ x ∈ s, g x = x

/-- Equality of kernels on the same original subgroup. -/
def SameAction (H : Subgroup (Equiv.Perm X)) (s t : Set X) : Prop :=
  ∀ g ∈ H, Fixes g s ↔ Fixes g t

def IsDuplicate (H : Subgroup (Equiv.Perm X)) (s : Finset (PairOrbit H)) : Prop :=
  s.card = 2 ∧ ∀ a ∈ s, ∀ b ∈ s, SameAction H a.val b.val

abbrev DuplicateMark (H : Subgroup (Equiv.Perm X)) :=
  {s : Finset (PairOrbit H) // IsDuplicate H s}

theorem orbit_relabel (e : X ≃ Y) (H : Subgroup (Equiv.Perm X)) (x : X) :
    MulAction.orbit (relabelSubgroup e H) (e x) = e '' MulAction.orbit H x := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    let u : H := ⟨e.symm.permCongr g.val,
      (mem_relabelSubgroup e H g.val).mp g.property⟩
    refine ⟨u.val x, ⟨u, rfl⟩, ?_⟩
    change e (e.symm (g.val (e x))) = g.val (e x)
    exact e.apply_symm_apply _
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    let u : relabelSubgroup e H := ⟨e.permCongr g.val, by
      apply (mem_relabelSubgroup e H _).mpr
      have he : e.symm.permCongr (e.permCongr g.val) = g.val := by
        ext z
        simp
      rw [he]
      exact g.property⟩
    refine ⟨u, ?_⟩
    change e (g.val (e.symm (e x))) = e (g.val x)
    rw [e.symm_apply_apply]

theorem isPairOrbit_image_iff (e : X ≃ Y) (H : Subgroup (Equiv.Perm X))
    (s : Set X) : IsPairOrbit (relabelSubgroup e H) (e '' s) ↔ IsPairOrbit H s := by
  constructor
  · rintro ⟨⟨y, hy⟩, hc⟩
    refine ⟨⟨e.symm y, ?_⟩, ?_⟩
    · apply e.injective.image_injective
      rw [hy, ← orbit_relabel, e.apply_symm_apply]
    · exact (Nat.card_congr (Equiv.image e s)).trans hc
  · rintro ⟨⟨x, rfl⟩, hc⟩
    refine ⟨⟨e x, (orbit_relabel e H x).symm⟩, ?_⟩
    exact (Nat.card_congr (Equiv.image e (MulAction.orbit H x))).symm.trans hc

/-- Literal image of the original orbit subset, with no chart choices. -/
def pairOrbitEquiv (e : X ≃ Y) (H : Subgroup (Equiv.Perm X)) :
    PairOrbit H ≃ PairOrbit (relabelSubgroup e H) :=
  (Equiv.Set.congr e).subtypeEquiv (fun s => (isPairOrbit_image_iff e H s).symm)

@[simp] theorem pairOrbitEquiv_val (e : X ≃ Y) (H : Subgroup (Equiv.Perm X))
    (s : PairOrbit H) : (pairOrbitEquiv e H s).val = e '' s.val := rfl

theorem fixes_image_iff (e : X ≃ Y) (g : Equiv.Perm X) (s : Set X) :
    Fixes (e.permCongr g) (e '' s) ↔ Fixes g s := by
  constructor
  · intro h x hx
    have he := h (e x) ⟨x, hx, rfl⟩
    apply e.injective
    simpa using he
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using congrArg e (h x hx)

theorem sameAction_image_iff (e : X ≃ Y) (H : Subgroup (Equiv.Perm X))
    (s t : Set X) :
    SameAction (relabelSubgroup e H) (e '' s) (e '' t) ↔ SameAction H s t := by
  constructor
  · intro h g hg
    have hmem : e.permCongr g ∈ relabelSubgroup e H := by
      apply (mem_relabelSubgroup e H _).mpr
      have he : e.symm.permCongr (e.permCongr g) = g := by ext z; simp
      rw [he]
      exact hg
    simpa only [fixes_image_iff] using h (e.permCongr g) hmem
  · intro h g hg
    let u := e.symm.permCongr g
    have hu : u ∈ H := (mem_relabelSubgroup e H g).mp hg
    have he : e.permCongr u = g := by ext y; simp [u]
    rw [← he, fixes_image_iff, fixes_image_iff]
    exact h u hu

theorem isDuplicate_map_iff (e : X ≃ Y) (H : Subgroup (Equiv.Perm X))
    (s : Finset (PairOrbit H)) :
    IsDuplicate (relabelSubgroup e H) (s.map (pairOrbitEquiv e H).toEmbedding) ↔
      IsDuplicate H s := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨by simpa using hc, ?_⟩
    intro a ha b hb
    have hab := h (pairOrbitEquiv e H a) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
      (pairOrbitEquiv e H b) (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
    exact (sameAction_image_iff e H a.val b.val).mp hab
  · rintro ⟨hc, h⟩
    refine ⟨by simpa using hc, ?_⟩
    intro a ha b hb
    obtain ⟨a, ha0, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b, hb0, rfl⟩ := Finset.mem_map.mp hb
    exact (sameAction_image_iff e H a.val b.val).mpr (h a ha0 b hb0)

/-- A selected unordered duplicate pair is transported by the actual point
relabeling. This supplies finite-mark naturality for profile assembly. -/
def duplicateMarkEquiv (e : X ≃ Y) (H : Subgroup (Equiv.Perm X)) :
    DuplicateMark H ≃ DuplicateMark (relabelSubgroup e H) :=
  (pairOrbitEquiv e H).finsetCongr.subtypeEquiv
    (fun s => (isDuplicate_map_iff e H s).symm)

theorem duplicateMark_card_relabel (e : X ≃ Y) (H : Subgroup (Equiv.Perm X)) :
    Nat.card (DuplicateMark (relabelSubgroup e H)) = Nat.card (DuplicateMark H) :=
  (Nat.card_congr (duplicateMarkEquiv e H)).symm

section Assembly

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}

/-- Actual physical duplicate-pair incidence has the original atlas weight.
No orientation, ordering of the selected pair, or extra orbit presentation
is counted in the left side. -/
theorem duplicate_incidence_assembly
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    Nat.card (Σ H : AssembledOrbitProfile P, DuplicateMark H.val) =
      Nat.card (LabelledOrbitAtlas Ω m U) *
        Nat.card (Σ K : {K // P K}, DuplicateMark K.val) :=
  assembledOrbitProfile_marked_card hfull hnatural htrans hsep DuplicateMark
    (fun e H => (duplicateMarkEquiv e H).symm)

end Assembly

end SymmetricSubgroupAsymptotics.PermutationPairOrbitMarks
