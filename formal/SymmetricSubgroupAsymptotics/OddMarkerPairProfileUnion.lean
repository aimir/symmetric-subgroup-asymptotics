import SymmetricSubgroupAsymptotics.OddMarkerPairPhysicalIncidence
import SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfileUnion

/-!
# Natural-marker incidence on common labels and profile unions

The fixed-profile one-third identity is transported to literal finite
point sets and summed over any finite selection of retained complete binary
profiles.  The source has one natural `S_3` orbit; the target replaces it by
one additional actual pair orbit and remembers a point in the set of such
orbits.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.OddMarkerPairProfileUnion

open RepeatedMarkerMergedProfile
open OddMarkerPairModelEquiv
open OddMarkerPairPhysicalIncidence
open PermutationPairOrbitMarks

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

local instance finiteSubgroups (G : Type*) [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

abbrev OddPhysicalOn (m : α → ℕ) (p : ℕ) (X : Type) :=
  AssembledOrbitProfileOn
    (OrbitProfileFull (OddAction Ω U) (m := OddMultiplicity m p) 1) X

local instance oddPhysicalOnFinite (m : α → ℕ) (p : ℕ) (X : Type) [Finite X] :
    Finite (OddPhysicalOn Ω U m p X) :=
  Finite.of_injective
    (fun H : OddPhysicalOn Ω U m p X => (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance oddPhysicalOnFintype (m : α → ℕ) (p : ℕ) (X : Type) [Finite X] :
    Fintype (OddPhysicalOn Ω U m p X) :=
  @Fintype.ofFinite (OddPhysicalOn Ω U m p X) (oddPhysicalOnFinite Ω U m p X)

def oddPhysicalEquivOn (m : α → ℕ) (p : ℕ) {X : Type}
    (e : OddModelPoints Ω m p ≃ X) :
    OddPhysical Ω m U p ≃ OddPhysicalOn Ω U m p X :=
  (assembledFullOrbitProfileEquiv (OddAction Ω U)).symm |>.trans
    ((assembledOrbitProfileEquivOn
      (OrbitProfileFull (OddAction Ω U) (m := OddMultiplicity m p) 1)
      (Equiv.refl (OddModelPoints Ω m p))).symm.trans
    (assembledOrbitProfileEquivOn
      (OrbitProfileFull (OddAction Ω U) (m := OddMultiplicity m p) 1) e))

local instance binaryPhysicalOnFinite (m : α → ℕ) (p : ℕ) (X : Type) [Finite X] :
    Finite (BinaryDuplicatePairProfileUnion.PhysicalOn Ω U m p X) :=
  Finite.of_injective
    (fun H : BinaryDuplicatePairProfileUnion.PhysicalOn Ω U m p X =>
      (H.val : Set (Equiv.Perm X)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance binaryPhysicalOnFintype (m : α → ℕ) (p : ℕ) (X : Type) [Finite X] :
    Fintype (BinaryDuplicatePairProfileUnion.PhysicalOn Ω U m p X) :=
  @Fintype.ofFinite (BinaryDuplicatePairProfileUnion.PhysicalOn Ω U m p X)
    (binaryPhysicalOnFinite Ω U m p X)

def oddFinChart (m : α → ℕ) (p d : ℕ)
    (hd : 2*(p+1) + exteriorDegree Ω m = d) :
    OddModelPoints Ω m p ≃ Fin (d+1) := by
  apply orbitProfileFinLabels (OddPoints Ω) (OddMultiplicity m p) (d+1)
  rw [RepeatedOddMarkerPhysicalProfile.physicalDegree,
    RepeatedMarkerMergedProfile.degree Ω m p]
  omega

theorem normalized_incidence_fin (m : α → ℕ) (p d : ℕ)
    (hd : 2*(p+1) + exteriorDegree Ω m = d)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (OddPhysicalOn Ω U m p (Fin (d+1))) : ℚ) / (d+1).factorial =
      (1/3 : ℚ) *
        ((∑ H : BinaryDuplicatePairProfileUnion.PhysicalOn Ω U m (p+1) (Fin d),
          (Nat.card (PairOrbit H.val) : ℚ)) / d.factorial) := by
  rw [← Nat.card_congr (oddPhysicalEquivOn Ω U m p (oddFinChart Ω m p d hd)),
    BinaryDuplicatePairProfileUnion.pointed_sum_on Ω U m (p+1)
      (BinaryDuplicatePairProfileUnion.finChart Ω m (p+1) d hd)]
  have h := normalized_odd_pair_incidence Ω m U p hU htrans hsep hdegree
  simpa only [hd,show 3 + 2*p + exteriorDegree Ω m = d+1 by omega] using h

abbrev Profile := BinaryDuplicatePairProfileUnion.Profile (α := α)

def oddMultiplicity (t : Profile (α := α)) :
    PUnit.{1} ⊕ (PUnit.{1} ⊕ α) → ℕ :=
  OddMultiplicity t.2 t.1

theorem oddMultiplicity_injective :
    Function.Injective (oddMultiplicity (α := α)) := by
  intro t s h
  apply Prod.ext
  · exact congrFun h (.inr (.inl PUnit.unit))
  · funext a
    exact congrFun h (.inr (.inr a))

abbrev OddSelectedFamily (d : ℕ) (S : Finset (Profile (α := α))) :=
  AssembledOrbitProfilesOn
    (fun t : S => oddMultiplicity t.val)
    (fun t => OrbitProfileFull (OddAction Ω U) (m := oddMultiplicity t.val) 1)
    (Fin (d+1))

local instance oddSelectedFamilyFinite (d : ℕ) (S : Finset (Profile (α := α))) :
    Finite (OddSelectedFamily Ω U d S) :=
  Finite.of_injective
    (fun H : OddSelectedFamily Ω U d S =>
      (H.val : Set (Equiv.Perm (Fin (d+1)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance oddSelectedFamilyFintype (d : ℕ) (S : Finset (Profile (α := α))) :
    Fintype (OddSelectedFamily Ω U d S) :=
  @Fintype.ofFinite (OddSelectedFamily Ω U d S)
    (oddSelectedFamilyFinite Ω U d S)

local instance binarySelectedFamilyFinite (k d : ℕ)
    (S : Finset (Profile (α := α))) :
    Finite (BinaryDuplicatePairProfileUnion.SelectedFamily Ω U k d S) :=
  Finite.of_injective
    (fun H : BinaryDuplicatePairProfileUnion.SelectedFamily Ω U k d S =>
      (H.val : Set (Equiv.Perm (Fin d))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance binarySelectedFamilyFintype (k d : ℕ)
    (S : Finset (Profile (α := α))) :
    Fintype (BinaryDuplicatePairProfileUnion.SelectedFamily Ω U k d S) :=
  @Fintype.ofFinite (BinaryDuplicatePairProfileUnion.SelectedFamily Ω U k d S)
    (binarySelectedFamilyFinite Ω U k d S)

private theorem baseAction_isPGroup (hU : ∀ a, IsPGroup 2 (U a)) :
    ∀ i, IsPGroup 2 (BaseAction Ω U i) := by
  have hsign : IsPGroup 2 RepeatedMarkerMergedProfile.Sign := by
    intro x
    refine ⟨1, ?_⟩
    simpa only [pow_one] using binary_mul_pow_two x
  intro i
  cases i with
  | inl _ => exact hsign.of_equiv binaryMarkerLocalEquiv
  | inr a => exact hU a

private theorem oddAction_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ i (x y : OddPoints Ω i), ∃ u : OddAction Ω U i,
      (u : Equiv.Perm (OddPoints Ω i)) x = y :=
  RepeatedOddMarkerPhysicalProfile.action_transitive
    (BasePoints Ω) (BaseAction Ω U)
    (RepeatedMarkerMergedProfile.action_transitive Ω U htrans)

private theorem oddAction_separated
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    OrbitActionTypesSeparated (OddPoints Ω) (OddAction Ω U) := by
  apply RepeatedOddMarkerPhysicalProfile.action_separated
    (BasePoints Ω) (BaseAction Ω U)
    (RepeatedMarkerMergedProfile.action_separated Ω U hsep hdegree)
  intro i
  cases i with
  | inl _ =>
      rw [RepeatedMarkerMergedProfile.point_card_pair]
      decide
  | inr a =>
      exact RepeatedOddMarkerPhysicalBinary.exteriorDegree_ne_three Ω U hU htrans a

def oddSelectedSigmaEquiv (d : ℕ) (S : Finset (Profile (α := α)))
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Σ t : S, OddPhysicalOn Ω U t.val.2 t.val.1 (Fin (d+1))) ≃
      OddSelectedFamily Ω U d S :=
  assembledOrbitProfilesSigmaEquiv
    (fun t s h => Subtype.ext (oddMultiplicity_injective h))
    (fun _ _ h => h) (oddAction_transitive Ω U htrans)
    (oddAction_separated Ω U hU htrans hsep hdegree)

theorem oddSelected_card_sum (d : ℕ) (S : Finset (Profile (α := α)))
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (OddSelectedFamily Ω U d S) : ℚ) =
      ∑ t : S, (Nat.card
        (OddPhysicalOn Ω U t.val.2 t.val.1 (Fin (d+1))) : ℚ) := by
  rw [← Nat.card_congr (oddSelectedSigmaEquiv Ω U d S hU htrans hsep hdegree),
    Nat.card_sigma,Nat.cast_sum]

/-- Exact one-third incidence after forgetting the selected profile index.
Both sides consist of literal original permutation subgroups. -/
theorem normalized_selected_incidence (d : ℕ)
    (S : Finset (Profile (α := α)))
    (hsize : ∀ t ∈ S, 2*(t.1+1) + exteriorDegree Ω t.2 = d)
    (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (OddSelectedFamily Ω U d S) : ℚ) / (d+1).factorial =
      (1/3 : ℚ) *
        ((∑ H : BinaryDuplicatePairProfileUnion.SelectedFamily Ω U 1 d S,
          (Nat.card (PairOrbit H.val) : ℚ)) / d.factorial) := by
  rw [oddSelected_card_sum Ω U d S hU htrans hsep hdegree,
    BinaryDuplicatePairProfileUnion.selected_weight_sum Ω U 1 d S
      htrans hsep hdegree
      (fun H : Subgroup (Equiv.Perm (Fin d)) => (Nat.card (PairOrbit H) : ℚ)),
    Finset.sum_div]
  calc
    _ = ∑ t : S, (1/3 : ℚ) *
        ((∑ H : BinaryDuplicatePairProfileUnion.PhysicalOn
          Ω U t.val.2 (t.val.1+1) (Fin d),
          (Nat.card (PairOrbit H.val) : ℚ)) / d.factorial) := by
      apply Finset.sum_congr rfl
      intro t _
      exact normalized_incidence_fin Ω U t.val.2 t.val.1 d
        (hsize t.val t.property) hU htrans hsep hdegree
    _ = _ := by rw [← Finset.mul_sum,← Finset.sum_div]

end SymmetricSubgroupAsymptotics.OddMarkerPairProfileUnion

end
