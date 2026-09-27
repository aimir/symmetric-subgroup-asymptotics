import SymmetricSubgroupAsymptotics.CriticalActionModels
import SymmetricSubgroupAsymptotics.IndependentCharacterCoordinates
import SymmetricSubgroupAsymptotics.CarrierEpimorphismPullback
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Four independent original pair coordinates and the actual E8 action

The full preimage under the exact Heisenberg quotient reconstructs the
original subgroup and keeps its entire exterior image. Independence is
tested on the four characters of that original subgroup and supplies joint
surjectivity; no joint-fullness premise is inserted. This is the local
map/comap construction of CarrierEpimorphismPullback, specialized directly
to one cover factor so that no extra singleton coordinate chart is needed.
It does not yet assert the global labelled four-orbit incidence.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourPairE8Model

abbrev Sign := Multiplicative (ZMod 2)
abbrev Four := Fin 4 → Sign
abbrev E8 := criticalActionSubgroup .e8

/-- Faithful coordinates of the same original eight-point permutation group. -/
def coordinates : E8 ≃* BinaryHeisenberg 2 :=
  (MonoidHom.ofInjective (BinaryHeisenberg.action_injective 2)).symm

/-- The fixed interleaved quotient coordinates (a0,b0,a1,b1). -/
def quotientChart :
    Multiplicative ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2)) ≃* Four :=
  e8QuotientChart.toAddEquiv.toMultiplicative.trans
    (MulEquiv.piMultiplicative (fun _ : Fin 4 => ZMod 2))

def quotient : E8 →* Four :=
  quotientChart.toMonoidHom.comp
    ((BinaryHeisenberg.quotient 2).comp coordinates.toMonoidHom)

@[simp] theorem quotient_apply (g : E8) (i : Fin 4) :
    quotient g i = Multiplicative.ofAdd
      (e8QuotientChart ((coordinates g).a, (coordinates g).b) i) := rfl

theorem quotient_surjective : Function.Surjective quotient :=
  quotientChart.surjective.comp
    ((BinaryHeisenberg.quotient_surjective 2).comp coordinates.surjective)

theorem coordinates_mem_center (g : E8) :
    g ∈ Subgroup.center E8 ↔ coordinates g ∈ Subgroup.center (BinaryHeisenberg 2) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := coordinates.surjective x
    simpa only [map_mul] using congrArg coordinates (h y)
  · intro h y
    apply coordinates.injective
    simpa only [map_mul] using h (coordinates y)

/-- The quotient kernel is the actual local center, not the center of an
arbitrary subgroup of an exterior product. -/
theorem quotient_ker_eq_center : quotient.ker = Subgroup.center E8 := by
  ext g
  change quotientChart (BinaryHeisenberg.quotient 2 (coordinates g)) = 1 ↔ _
  rw [quotientChart.map_eq_one_iff]
  change coordinates g ∈ (BinaryHeisenberg.quotient 2).ker ↔ _
  rw [← BinaryHeisenberg.center_eq_quotient_ker]
  exact (coordinates_mem_center g).symm

variable {D : Type*} [Group D]

/-- The four scalar characters on one literal original subgroup. -/
def character (H : Subgroup (Four × D)) (i : Fin 4) : PrimeCharacters 2 H where
  toFun g := (g.toMul.val.1 i).toAdd
  map_zero' := rfl
  map_add' _ _ := rfl

def Independent (H : Subgroup (Four × D)) : Prop :=
  LinearIndependent (ZMod 2) (character H)

theorem joint_eq_projection (H : Subgroup (Four × D)) :
    IndependentCharacterCoordinates.joint 2 (character H) =
      (MonoidHom.fst Four D).comp H.subtype := rfl

/-- Joint fullness follows from original independence, rather than being
supplied separately or inferred from four individual surjections. -/
theorem original_projection_surjective [Finite D] (H : Subgroup (Four × D))
    (hH : Independent H) :
    Function.Surjective ((MonoidHom.fst Four D).comp H.subtype) := by
  rw [← joint_eq_projection]
  exact IndependentCharacterCoordinates.binary_joint_surjective (character H) hH

/-- The complete exterior coordinate is literally unchanged. -/
def productMap : (E8 × D) →* (Four × D) := quotient.prodMap (MonoidHom.id D)

@[simp] theorem productMap_apply (g : E8) (d : D) :
    productMap (g, d) = (quotient g, d) := rfl

theorem productMap_surjective : Function.Surjective (productMap (D := D)) := by
  rintro ⟨v, d⟩
  obtain ⟨g, rfl⟩ := quotient_surjective v
  exact ⟨(g, d), rfl⟩

def lift (H : Subgroup (Four × D)) : Subgroup (E8 × D) := H.comap productMap

theorem reconstruct (H : Subgroup (Four × D)) :
    (lift H).map productMap = H :=
  Subgroup.map_comap_eq_self_of_surjective productMap_surjective H

theorem exterior_image (H : Subgroup (Four × D)) :
    (lift H).map (MonoidHom.snd E8 D) = H.map (MonoidHom.snd Four D) := by
  calc
    _ = ((lift H).map productMap).map (MonoidHom.snd Four D) := by
      rw [Subgroup.map_map]
      rfl
    _ = _ := by rw [reconstruct]

/-- Prescribe any element of the entire actual E8 action. The original
onto joint character tuple supplies a simultaneous lift with the same
exterior coordinate. -/
theorem lift_full [Finite D] (H : Subgroup (Four × D)) (hH : Independent H) :
    (lift H).map (MonoidHom.fst E8 D) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨x, hx⟩ := original_projection_surjective H hH (quotient g)
  refine Subgroup.mem_map.mpr ⟨(g, x.val.2), ?_, rfl⟩
  change (quotient g, x.val.2) ∈ H
  have he : (quotient g, x.val.2) = x.val := Prod.ext hx.symm rfl
  rw [he]
  exact x.property

/-- Every original normal relation or extra exclusion may be retained on
the full reconstructed subgroup, in addition to the exterior predicate. -/
abbrev OriginalFamily (P : Subgroup D → Prop) (R : Subgroup (Four × D) → Prop) :=
  {H : Subgroup (Four × D) //
    Independent H ∧ P (H.map (MonoidHom.snd Four D)) ∧ R H}

abbrev CoverFamily (P : Subgroup D → Prop) (R : Subgroup (Four × D) → Prop) :=
  {K : Subgroup (E8 × D) // K.map (MonoidHom.fst E8 D) = ⊤ ∧
    P (K.map (MonoidHom.snd E8 D)) ∧ R (K.map productMap)}

def familyEmbedding [Finite D] (P : Subgroup D → Prop)
    (R : Subgroup (Four × D) → Prop) : OriginalFamily P R ↪ CoverFamily P R where
  toFun H := ⟨lift H.val, lift_full H.val H.property.1, by
      rw [exterior_image]
      exact H.property.2.1, by
      rw [reconstruct]
      exact H.property.2.2⟩
  inj' := by
    intro H K h
    have he := congrArg (fun L : CoverFamily P R => L.val.map productMap) h
    change (lift H.val).map productMap = (lift K.val).map productMap at he
    apply Subtype.ext
    simpa only [reconstruct] using he

@[simp] theorem familyEmbedding_original [Finite D] (P : Subgroup D → Prop)
    (R : Subgroup (Four × D) → Prop) (H : OriginalFamily P R) :
    (familyEmbedding P R H).val.map productMap = H.val := reconstruct H.val

theorem familyEmbedding_exterior [Finite D] (P : Subgroup D → Prop)
    (R : Subgroup (Four × D) → Prop) (H : OriginalFamily P R) :
    (familyEmbedding P R H).val.map (MonoidHom.snd E8 D) =
      H.val.map (MonoidHom.snd Four D) := exterior_image H.val

local instance coverSubgroupsFinite [Finite D] : Finite (Subgroup (E8 × D)) :=
  Finite.of_injective (fun K : Subgroup (E8 × D) => (K : Set (E8 × D)))
    SetLike.coe_injective

/-- Only the proved original subgroup embedding supplies this count. The
cover family may contain further full E8 subgroups. -/
theorem family_card_le [Finite D] (P : Subgroup D → Prop)
    (R : Subgroup (Four × D) → Prop) :
    Nat.card (OriginalFamily P R) ≤ Nat.card (CoverFamily P R) :=
  Nat.card_le_card_of_injective (familyEmbedding P R) (familyEmbedding P R).injective

end SymmetricSubgroupAsymptotics.BinaryFourPairE8Model
