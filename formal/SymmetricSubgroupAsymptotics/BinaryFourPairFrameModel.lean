import SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfile
import SymmetricSubgroupAsymptotics.PermutationPairOrbitCharacters
import SymmetricSubgroupAsymptotics.BinaryFourPairSelectedModel

/-!
# Actual independent pair-orbit frames and original coordinates

For a complete original profile with one two-point color, every actual
two-point orbit is one original occurrence.  Its canonical binary character,
pulled back through the faithful product action, is the displayed scalar
coordinate.  Thus actual ordered independent frames are exactly the ordered
coordinate selections used by the reversible E8 construction.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryFourPairFrameModel

open RepeatedMarkerMergedProfile RepeatedCharacterCollapse
open PermutationPairOrbitMarks PermutationPairOrbitCharacters

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

abbrev SignFamily (p : ℕ) := BinaryDuplicatePairProfile.SignFamily Ω m U p
abbrev Model (p : ℕ) := BinaryDuplicatePairProfile.Model Ω m U p

/-- The faithful original-coordinate model and the literal permutation model
carry isomorphic copies of the same subgroup. -/
def modelGroupEquiv (p : ℕ) (Y : SignFamily Ω m U p) :
    Y.val ≃* (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val :=
  (Subgroup.equivMapOfInjective Y.val
      (BinaryDuplicatePairProfile.originalChart Ω m U p).toMonoidHom
      (BinaryDuplicatePairProfile.originalChart Ω m U p).injective).trans
    (Subgroup.equivMapOfInjective
      (Y.val.map (BinaryDuplicatePairProfile.originalChart Ω m U p).toMonoidHom)
      (orbitProfileProductAction (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U))
      (orbitProfileProductAction_injective
        (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U)))

@[simp] theorem modelGroupEquiv_coe (p : ℕ) (Y : SignFamily Ω m U p) (y : Y.val) :
    ((modelGroupEquiv Ω m U p Y y :
      (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val) :
      Equiv.Perm (ModelPoints Ω m p)) =
      orbitProfileProductAction (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U)
        (BinaryDuplicatePairProfile.originalChart Ω m U p y.val) := rfl

/-- The displayed scalar coordinate as an additive binary character of the
same original subgroup. -/
def coordinateCharacter (p : ℕ) (Y : SignFamily Ω m U p) (j : Fin p) :
    PrimeCharacters 2 Y.val where
  toFun y := (y.toMul.val.1 j).toAdd
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem binary_eq_iff (a b : ZMod 2) : (a = 0 ↔ b = 0) ↔ a = b := by
  have h : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) ↔ a = b := by decide
  exact h a b

theorem coordinateCharacter_ne_zero (p : ℕ) (Y : SignFamily Ω m U p) (j : Fin p) :
    coordinateCharacter Ω m U p Y j ≠ 0 := by
  intro h
  have hs := Y.property.1 j
  obtain ⟨y,hy⟩ := hs (Multiplicative.ofAdd (1 : ZMod 2))
  have hz := DFunLike.congr_fun h (Additive.ofMul y)
  change y.val.1 j = 1 at hz
  change y.val.1 j = Multiplicative.ofAdd 1 at hy
  rw [hy] at hz
  norm_num at hz

/-- Pullback of the actual orbit character is exactly the displayed original
coordinate.  The proof uses the literal fixing kernel, not a choice of orbit
orientation. -/
theorem character_pullback (p : ℕ) (Y : SignFamily Ω m U p)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) (j : Fin p) :
    primeCharacterCongr 2 (modelGroupEquiv Ω m U p Y)
      (character (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val
        (OrbitProfilePairMarks.pairOrbitEquiv
          (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).property
          (action_transitive Ω U htrans) (.inl PUnit.unit)
          (BinaryDuplicatePairProfile.pair_degree_iff Ω hdegree) j)) =
      coordinateCharacter Ω m U p Y j := by
  apply AddMonoidHom.ext
  intro y
  apply (binary_eq_iff _ _).mp
  change character (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val
      (OrbitProfilePairMarks.pairOrbitEquiv
        (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).property
        (action_transitive Ω U htrans) (.inl PUnit.unit)
        (BinaryDuplicatePairProfile.pair_degree_iff Ω hdegree) j)
      (Additive.ofMul (modelGroupEquiv Ω m U p Y y.toMul)) = 0 ↔
        y.toMul.val.1 j = 1
  rw [character_zero_iff]
  change Fixes
      (orbitProfileProductAction (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U)
        (BinaryDuplicatePairProfile.originalChart Ω m U p y.toMul.val))
      (OrbitProfilePairMarks.block (.inl PUnit.unit) j) ↔ y.toMul.val.1 j = 1
  rw [OrbitProfilePairMarks.fixes_product_block]
  change binaryMarkerLocalEquiv (y.val.1 j) = 1 ↔ y.val.1 j = 1
  rw [binaryMarkerLocalEquiv.map_eq_one_iff]

variable (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2)

def actualOccurrence (p : ℕ) (Y : SignFamily Ω m U p) (j : Fin p) :
    PairOrbit (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val :=
  OrbitProfilePairMarks.pairOrbitEquiv
    (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).property
    (action_transitive Ω U htrans) (.inl PUnit.unit)
    (BinaryDuplicatePairProfile.pair_degree_iff Ω hdegree) j

/-- Independence is transported through the faithful original subgroup,
with the actual pair orbit tied to its literal occurrence label. -/
theorem actual_independent_iff_coordinate (p : ℕ) (Y : SignFamily Ω m U p)
    (v : Fin 4 → Fin p) :
    LinearIndependent (ZMod 2) (fun i =>
      character (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val
        (actualOccurrence Ω m U htrans hdegree p Y (v i))) ↔
    LinearIndependent (ZMod 2) (fun i => coordinateCharacter Ω m U p Y (v i)) := by
  let f := primeCharacterCongr 2 (modelGroupEquiv Ω m U p Y)
  have he := f.toLinearMap.linearIndependent_iff_of_injOn
    (v := fun i => character (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val
      (actualOccurrence Ω m U htrans hdegree p Y (v i))) f.injective.injOn
  have hfun : ((f.toLinearMap : PrimeCharacters 2
      (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val →
        PrimeCharacters 2 Y.val) ∘
      (fun i => character (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val
        (actualOccurrence Ω m U htrans hdegree p Y (v i)))) =
      (fun i => coordinateCharacter Ω m U p Y (v i)) := by
    funext i
    exact character_pullback Ω m U p Y htrans hdegree (v i)
  rw [hfun] at he
  exact he.symm

abbrev CoordinateFrame (p : ℕ) (Y : SignFamily Ω m U p) :=
  {v : Fin 4 ↪ Fin p //
    LinearIndependent (ZMod 2) (fun i => coordinateCharacter Ω m U p Y (v i))}

def frameSelection (p : ℕ) (Y : SignFamily Ω m U p)
    (v : Frame (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val 4) : Fin 4 ↪ Fin p where
  toFun i := (OrbitProfilePairMarks.pairOrbitEquiv
    (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).property
    (action_transitive Ω U htrans) (.inl PUnit.unit)
    (BinaryDuplicatePairProfile.pair_degree_iff Ω hdegree)).symm (v.val i)
  inj' i j hij := by
    apply frame_injective (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val v
    exact (OrbitProfilePairMarks.pairOrbitEquiv
      (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).property
      (action_transitive Ω U htrans) (.inl PUnit.unit)
      (BinaryDuplicatePairProfile.pair_degree_iff Ω hdegree)).symm.injective hij

@[simp] theorem actualOccurrence_frameSelection (p : ℕ) (Y : SignFamily Ω m U p)
    (v : Frame (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val 4) (i : Fin 4) :
    actualOccurrence Ω m U htrans hdegree p Y (frameSelection Ω m U htrans hdegree p Y v i) =
      v.val i :=
  (OrbitProfilePairMarks.pairOrbitEquiv
    (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).property
    (action_transitive Ω U htrans) (.inl PUnit.unit)
    (BinaryDuplicatePairProfile.pair_degree_iff Ω hdegree)).apply_symm_apply (v.val i)

/-- Actual ordered independent pair-orbit frames are exactly original ordered
coordinate selections. -/
def frameEquivCoordinate (p : ℕ) (Y : SignFamily Ω m U p) :
    Frame (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).val 4 ≃
      CoordinateFrame Ω m U p Y where
  toFun v := ⟨frameSelection Ω m U htrans hdegree p Y v,
    (actual_independent_iff_coordinate Ω m U htrans hdegree p Y _).mp (by
      simpa only [actualOccurrence_frameSelection] using v.property)⟩
  invFun v := ⟨fun i => actualOccurrence Ω m U htrans hdegree p Y (v.val i),
    (actual_independent_iff_coordinate Ω m U htrans hdegree p Y _).mpr v.property⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    exact actualOccurrence_frameSelection Ω m U htrans hdegree p Y v i
  right_inv v := by
    apply Subtype.ext
    exact Function.Embedding.ext fun i =>
      (OrbitProfilePairMarks.pairOrbitEquiv
        (BinaryDuplicatePairProfile.modelEquiv Ω m U p Y).property
        (action_transitive Ω U htrans) (.inl PUnit.unit)
      (BinaryDuplicatePairProfile.pair_degree_iff Ω hdegree)).symm_apply_apply (v.val i)

/-- The full sign/exterior family is definitionally the source family used by
the selected-coordinate E8 construction, after spelling fullness as a top
image. -/
def signFamilyEquivOriginal (n : ℕ) :
    SignFamily Ω m U (n+4) ≃
      BinaryFourPairSelectedModel.OriginalFamily
        (D := Exterior Ω m U) n (OrbitProfileProductFull m U) (fun _ => True) where
  toFun Y := ⟨Y.val, fun j => by
      apply top_unique
      intro z _
      obtain ⟨y,hy⟩ := Y.property.1 j z
      exact Subgroup.mem_map.mpr ⟨y.val,y.property,hy⟩,
    Y.property.2, True.intro⟩
  invFun Y := ⟨Y.val, fun j z => by
      have hz : z ∈ Y.val.map (BinaryFourPairSelectedModel.coordinate j) := by
        rw [Y.property.1 j]
        trivial
      obtain ⟨y,hy,he⟩ := Subgroup.mem_map.mp hz
      exact ⟨⟨y,hy⟩,he⟩,
    Y.property.2.1⟩
  left_inv Y := rfl
  right_inv Y := rfl

/-- Coordinate frames, summed over the complete source family, are exactly
the algebraic incidence consumed by the reversible selected E8 model. -/
def coordinateIncidenceEquiv (n : ℕ) :
    (Σ Y : SignFamily Ω m U (n+4), CoordinateFrame Ω m U (n+4) Y) ≃
      BinaryFourPairSelectedModel.Incidence (D := Exterior Ω m U) n
        (OrbitProfileProductFull m U) (fun _ => True) where
  toFun z := ⟨signFamilyEquivOriginal Ω m U n z.1,
    ⟨z.2.val, by
      change LinearIndependent (ZMod 2) (fun i =>
        coordinateCharacter Ω m U (n+4) z.1 (z.2.val i))
      exact z.2.property⟩⟩
  invFun z := ⟨(signFamilyEquivOriginal Ω m U n).symm z.1,
    ⟨z.2.val, by
      change LinearIndependent (ZMod 2) (fun i =>
        BinaryFourPairSelectedModel.character z.1.val (z.2.val i))
      exact z.2.property⟩⟩
  left_inv z := rfl
  right_inv z := rfl

/-- This is the complete fixed-profile bridge from physical model marks to
the selected-coordinate incidence. -/
def modelFrameIncidenceEquiv (n : ℕ) :
    (Σ K : Model Ω m U (n+4), Frame K.val 4) ≃
      BinaryFourPairSelectedModel.Incidence (D := Exterior Ω m U) n
        (OrbitProfileProductFull m U) (fun _ => True) :=
  (Equiv.sigmaCongr (BinaryDuplicatePairProfile.modelEquiv Ω m U (n+4))
      (fun _ => Equiv.refl _)).symm |>.trans
    ((Equiv.sigmaCongrRight fun Y => frameEquivCoordinate Ω m U htrans hdegree (n+4) Y).trans
      (coordinateIncidenceEquiv Ω m U n))

include htrans hdegree in
/-- The local reversible E8 injection now bounds actual ordered pair-orbit
frames on the complete fixed profile.  Original weights are installed later. -/
theorem model_frame_card_le (n : ℕ) :
    Nat.card (Σ K : Model Ω m U (n+4), Frame K.val 4) ≤
      (n+4).descFactorial 4 *
        Nat.card (BinaryFourPairSelectedModel.CoverFamily
          (D := Exterior Ω m U) n (OrbitProfileProductFull m U)) := by
  rw [Nat.card_congr (modelFrameIncidenceEquiv Ω m U htrans hdegree n)]
  exact BinaryFourPairSelectedModel.incidence_card_le n
    (OrbitProfileProductFull m U) (fun _ => True)

end SymmetricSubgroupAsymptotics.BinaryFourPairFrameModel
