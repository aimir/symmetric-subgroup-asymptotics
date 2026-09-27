import SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfile
import SymmetricSubgroupAsymptotics.BinaryExteriorOrbitMenu

/-!
# Duplicate-pair incidence on common labels and selected profile unions

The original physical marks are transported to the usual Fin point sets.
At a fixed total degree, a finite selection of complete exterior profiles
may then be summed exactly. The actual subgroup determines its complete
pair/exterior multiplicity vector, so the union forgets the profile index
without losing or multiplying a mark.

The final binary-menu instance proves action separation and transitivity
internally. The same selected exterior profiles occur on both sides. This
is the profile-predicate transport step: identifying a particular intrinsic
owner predicate with that profile selection remains a separate theorem.
In particular arbitrary exclusions are not declared collapse-invariant.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfileUnion

open RepeatedMarkerMergedProfile PermutationPairOrbitMarks

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

local instance finiteSubgroups (G : Type*) [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- The same complete original profile on a chosen actual point set. -/
abbrev PhysicalOn (m : α → ℕ) (p : ℕ) (X : Type) :=
  AssembledOrbitProfileOn
    (OrbitProfileFull (action Ω U)
      (m := RepeatedMarkerMergedProfile.multiplicity m p) 1) X

local instance physicalOnFinite (m : α → ℕ) (p : ℕ) (X : Type) [Finite X] :
    Finite (PhysicalOn Ω U m p X) :=
  Finite.of_injective
    (fun H : PhysicalOn Ω U m p X => (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance physicalOnFintype (m : α → ℕ) (p : ℕ) (X : Type) [Finite X] :
    Fintype (PhysicalOn Ω U m p X) :=
  @Fintype.ofFinite (PhysicalOn Ω U m p X) (physicalOnFinite Ω U m p X)

def physicalEquivOn (m : α → ℕ) (p : ℕ) {X : Type}
    (e : ModelPoints Ω m p ≃ X) :
    BinaryDuplicatePairProfile.Physical Ω m U p ≃ PhysicalOn Ω U m p X :=
  assembledOrbitProfileEquivOn _ e

@[simp] theorem physicalEquivOn_val (m : α → ℕ) (p : ℕ) {X : Type}
    (e : ModelPoints Ω m p ≃ X)
    (H : BinaryDuplicatePairProfile.Physical Ω m U p) :
    (physicalEquivOn Ω U m p e H).val = relabelSubgroup e H.val := rfl

/-- The actual selected unordered duplicate mark survives relabelling. -/
theorem duplicate_sum_on (m : α → ℕ) (p : ℕ) {X : Type} [Finite X]
    (e : ModelPoints Ω m p ≃ X) :
    (∑ H : PhysicalOn Ω U m p X, (Nat.card (DuplicateMark H.val) : ℚ)) =
      ∑ H : BinaryDuplicatePairProfile.Physical Ω m U p,
        (Nat.card (DuplicateMark H.val) : ℚ) := by
  apply (Fintype.sum_equiv (physicalEquivOn Ω U m p e) _ _ ?_).symm
  intro H
  rw [physicalEquivOn_val, duplicateMark_card_relabel]

/-- The target is still pointed at an actual two-point orbit. -/
theorem pointed_sum_on (m : α → ℕ) (p : ℕ) {X : Type} [Finite X]
    (e : ModelPoints Ω m p ≃ X) :
    (∑ H : PhysicalOn Ω U m p X, (Nat.card (PairOrbit H.val) : ℚ)) =
      ∑ H : BinaryDuplicatePairProfile.Physical Ω m U p,
        (Nat.card (PairOrbit H.val) : ℚ) := by
  apply (Fintype.sum_equiv (physicalEquivOn Ω U m p e) _ _ ?_).symm
  intro H
  rw [physicalEquivOn_val, ← Nat.card_congr (pairOrbitEquiv e H.val)]

def finChart (m : α → ℕ) (p d : ℕ)
    (hd : 2*p + exteriorDegree Ω m = d) : ModelPoints Ω m p ≃ Fin d :=
  orbitProfileFinLabels (points Ω) (RepeatedMarkerMergedProfile.multiplicity m p) d
    ((degree Ω m p).trans hd)

/-- One complete exterior profile, now on the literal Fin(N+2) and Fin N.
No point chart is supplied by the caller. -/
theorem normalized_incidence_fin (m : α → ℕ) (n d : ℕ)
    (hd : 2*(n+1) + exteriorDegree Ω m = d)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : PhysicalOn Ω U m (n+2) (Fin (d+2)),
      (Nat.card (DuplicateMark H.val) : ℚ)) / (d+2).factorial =
      (1/4 : ℚ) *
        ((∑ H : PhysicalOn Ω U m (n+1) (Fin d),
          (Nat.card (PairOrbit H.val) : ℚ)) / d.factorial) := by
  have hs : 2*(n+2) + exteriorDegree Ω m = d+2 := by omega
  rw [duplicate_sum_on Ω U m (n+2) (finChart Ω m (n+2) (d+2) hs),
    pointed_sum_on Ω U m (n+1) (finChart Ω m (n+1) d hd)]
  simpa only [hd,hs] using
    BinaryDuplicatePairProfile.normalized_duplicate_pointed_incidence
      Ω m U n htrans hsep hdegree

/-- The pair count before adding the source/target shift, and the entire
unchanged original exterior multiplicity vector. -/
abbrev Profile := ℕ × (α → ℕ)

def shiftedMultiplicity (k : ℕ) (t : Profile (α := α)) : PUnit.{1} ⊕ α → ℕ :=
  RepeatedMarkerMergedProfile.multiplicity t.2 (t.1+k)

theorem shiftedMultiplicity_injective (k : ℕ) :
    Function.Injective (shiftedMultiplicity (α := α) k) := by
  intro t s h
  apply Prod.ext
  · have hp := congrFun h (.inl PUnit.unit)
    change t.1+k = s.1+k at hp
    exact Nat.add_right_cancel hp
  · funext a
    exact congrFun h (.inr a)

/-- A profile selection is a predicate on the complete original exterior
data, represented by a finite set. No profile witness is counted. -/
abbrev SelectedFamily (k d : ℕ) (S : Finset (Profile (α := α))) :=
  AssembledOrbitProfilesOn
    (fun t : S => shiftedMultiplicity k t.val)
    (fun t => OrbitProfileFull (action Ω U) (m := shiftedMultiplicity k t.val) 1)
    (Fin d)

local instance selectedFamilyFinite (k d : ℕ) (S : Finset (Profile (α := α))) :
    Finite (SelectedFamily Ω U k d S) :=
  Finite.of_injective
    (fun H : SelectedFamily Ω U k d S => (H.val : Set (Equiv.Perm (Fin d))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance selectedFamilyFintype (k d : ℕ) (S : Finset (Profile (α := α))) :
    Fintype (SelectedFamily Ω U k d S) :=
  @Fintype.ofFinite (SelectedFamily Ω U k d S) (selectedFamilyFinite Ω U k d S)

/-- The actual subgroup determines the selected profile. Disjointness is
proved from original orbit actions, rather than supplied as a hypothesis. -/
def selectedSigmaEquiv (k d : ℕ) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Σ t : S, PhysicalOn Ω U t.val.2 (t.val.1+k) (Fin d)) ≃
      SelectedFamily Ω U k d S :=
  assembledOrbitProfilesSigmaEquiv
    (fun t s h => Subtype.ext (shiftedMultiplicity_injective k h))
    (fun _ _ h => h) (action_transitive Ω U htrans)
    (action_separated Ω U hsep hdegree)

@[simp] theorem selectedSigmaEquiv_val (k d : ℕ) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (z : Σ t : S, PhysicalOn Ω U t.val.2 (t.val.1+k) (Fin d)) :
    (selectedSigmaEquiv Ω U k d S htrans hsep hdegree z).val = z.2.val := rfl

/-- Any weight on the same original subgroup sums once across the selected
profiles. There is no naturality assumption because H itself is unchanged. -/
theorem selected_weight_sum (k d : ℕ) (S : Finset (Profile (α := α)))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)
    (w : Subgroup (Equiv.Perm (Fin d)) → ℚ) :
    (∑ H : SelectedFamily Ω U k d S, w H.val) =
      ∑ t : S, ∑ H : PhysicalOn Ω U t.val.2 (t.val.1+k) (Fin d), w H.val := by
  calc
    _ = ∑ z : (Σ t : S, PhysicalOn Ω U t.val.2 (t.val.1+k) (Fin d)), w z.2.val :=
      (Fintype.sum_equiv (selectedSigmaEquiv Ω U k d S htrans hsep hdegree)
        _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_sigma _

/-- Exact common-label incidence for any finite selected set of complete
exterior profiles. The same selection is retained through collapse. -/
theorem normalized_selected_incidence (d : ℕ) (S : Finset (Profile (α := α)))
    (hsize : ∀ t ∈ S, 2*(t.1+1) + exteriorDegree Ω t.2 = d)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : SelectedFamily Ω U 2 (d+2) S,
      (Nat.card (DuplicateMark H.val) : ℚ)) / (d+2).factorial =
      (1/4 : ℚ) *
        ((∑ H : SelectedFamily Ω U 1 d S,
          (Nat.card (PairOrbit H.val) : ℚ)) / d.factorial) := by
  have hs := selected_weight_sum Ω U 2 (d+2) S htrans hsep hdegree
    (fun H : Subgroup (Equiv.Perm (Fin (d+2))) => (Nat.card (DuplicateMark H) : ℚ))
  have ht := selected_weight_sum Ω U 1 d S htrans hsep hdegree
    (fun H : Subgroup (Equiv.Perm (Fin d)) => (Nat.card (PairOrbit H) : ℚ))
  dsimp only at hs ht
  rw [hs,ht,Finset.sum_div]
  calc
    _ = ∑ t : S, (1/4 : ℚ) *
        ((∑ H : PhysicalOn Ω U t.val.2 (t.val.1+1) (Fin d),
          (Nat.card (PairOrbit H.val) : ℚ)) / d.factorial) := by
      apply Finset.sum_congr rfl
      intro t _
      exact normalized_incidence_fin Ω U t.val.2 t.val.1 d
        (hsize t.val t.property) htrans hsep hdegree
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_div]

/-- The complete finite actual binary action menu supplies its own
separation and transitivity. The unchanged profile selector can encode
which original exterior actions are allowed, without any cardinal input.
This does not yet identify that selector with intrinsic noncriticality. -/
theorem binary_selected_incidence (bound d : ℕ)
    (S : Finset (Profile (α := BinaryExteriorOrbitMenu.Label bound)))
    (hsize : ∀ t ∈ S,
      2*(t.1+1) + exteriorDegree (BinaryExteriorOrbitMenu.points bound) t.2 = d) :
    (∑ H : SelectedFamily (BinaryExteriorOrbitMenu.points bound)
        (BinaryExteriorOrbitMenu.action bound) 2 (d+2) S,
      (Nat.card (DuplicateMark H.val) : ℚ)) / (d+2).factorial =
      (1/4 : ℚ) *
        ((∑ H : SelectedFamily (BinaryExteriorOrbitMenu.points bound)
            (BinaryExteriorOrbitMenu.action bound) 1 d S,
          (Nat.card (PairOrbit H.val) : ℚ)) / d.factorial) :=
  normalized_selected_incidence (BinaryExteriorOrbitMenu.points bound)
    (BinaryExteriorOrbitMenu.action bound) d S hsize
    (BinaryExteriorOrbitMenu.action_transitive bound)
    (BinaryExteriorOrbitMenu.action_separated bound)
    (BinaryExteriorOrbitMenu.point_card_ne_two bound)

end SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfileUnion

end
