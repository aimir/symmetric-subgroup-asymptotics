import SymmetricSubgroupAsymptotics.BinaryCarrierRoutes8
import SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions
import SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfileEpimorphism

/-! All seven original degree-eight carriers and five degree-sixteen
carriers are counted using their fixed master epimorphisms. Original
colors and occurrences stay distinct, including targets with the same
source master. Only the word bound uses the masters: physical points,
normalizers and multiplicity factorials belong to the original targets.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalActions

open BinaryCarrierWord

/-- Twelve original physical colors, not eight source-master colors. -/
inductive Target
  | degree8 (target : BinaryCarrierRoutes8.Target)
  | degree16 (master : BinaryCarrierMasterWords16.Master)
  deriving DecidableEq, Fintype

def points : Target → Type
  | .degree8 _ => Fin 8
  | .degree16 _ => Fin 16

instance (t : Target) : Fintype (points t) := by
  cases t <;> dsimp [points] <;> infer_instance

instance (t : Target) : Nonempty (points t) := by
  cases t <;> dsimp [points] <;> infer_instance

/-- The literal original permutation subgroup and generator order. -/
def action : (t : Target) → Subgroup (Equiv.Perm (points t))
  | .degree8 t => BinaryCarrierRoutes8.originalSubgroup t
  | .degree16 m => BinaryCarrierMixedActions.action (.degree16 m)

def masterKind : BinaryCarrierRoutes8.Master → BinaryCarrierMixedMenuWord.Kind
  | .x => .x
  | .j => .j
  | .p => .p

def sourceKind : Target → BinaryCarrierMixedMenuWord.Kind
  | .degree8 t => masterKind (BinaryCarrierRoutes8.sourceMaster t)
  | .degree16 m => .degree16 m

def sourceFactor (t : Target) : Factor := BinaryCarrierMixedMenuWord.factor (sourceKind t)

/-- Each original color has its fixed onto map. The degree-sixteen maps
are identities on the same actual group; no action conjugacy is invoked. -/
def hom : (t : Target) → (sourceFactor t).Carrier →* action t
  | .degree8 .t18 => BinaryCarrierRoutes8.hom .t18
  | .degree8 .t26 => BinaryCarrierRoutes8.hom .t26
  | .degree8 .t27 => BinaryCarrierRoutes8.hom .t27
  | .degree8 .t28 => BinaryCarrierRoutes8.hom .t28
  | .degree8 .t29 => BinaryCarrierRoutes8.hom .t29
  | .degree8 .t31 => BinaryCarrierRoutes8.hom .t31
  | .degree8 .t35 => BinaryCarrierRoutes8.hom .t35
  | .degree16 .t1082 => MonoidHom.id _
  | .degree16 .t1083 => MonoidHom.id _
  | .degree16 .t1084 => MonoidHom.id _
  | .degree16 .t1332 => MonoidHom.id _
  | .degree16 .t1547 => MonoidHom.id _

theorem hom_surjective (t : Target) : Function.Surjective (hom t) := by
  cases t with
  | degree8 t =>
      cases t with
      | t18 => exact BinaryCarrierRoutes8.hom_surjective .t18
      | t26 => exact BinaryCarrierRoutes8.hom_surjective .t26
      | t27 => exact BinaryCarrierRoutes8.hom_surjective .t27
      | t28 => exact BinaryCarrierRoutes8.hom_surjective .t28
      | t29 => exact BinaryCarrierRoutes8.hom_surjective .t29
      | t31 => exact BinaryCarrierRoutes8.hom_surjective .t31
      | t35 => exact BinaryCarrierRoutes8.hom_surjective .t35
  | degree16 m => cases m <;> intro x <;> exact ⟨x, rfl⟩

theorem action_binary (t : Target) : IsPGroup 2 (action t) :=
  (sourceFactor t).binary.of_surjective (hom t) (hom_surjective t)

def factorScaleNat : Target → ℕ
  | .degree8 _ => 1
  | .degree16 _ => 2

theorem factorScaleNat_cast (t : Target) :
    (factorScaleNat t : ℝ) = BinaryCarrierMixedMenuWord.factorScale (sourceKind t) := by
  cases t with
  | degree8 t =>
      cases t <;> norm_num [factorScaleNat, sourceKind, masterKind,
        BinaryCarrierRoutes8.sourceMaster, BinaryCarrierMixedMenuWord.factorScale]
  | degree16 m => norm_num [factorScaleNat, sourceKind, BinaryCarrierMixedMenuWord.factorScale]

theorem point_card (t : Target) : Fintype.card (points t) = 8 * factorScaleNat t := by
  cases t <;> rfl

/-- Multiplicities are indexed by all twelve original colors. Equal source
masters never identify a pair of target multiplicity factorials. -/
def scale (m : Target → ℕ) : ℕ := ∑ t, m t * factorScaleNat t

theorem scale_cast (m : Target → ℕ) :
    (scale m : ℝ) =
      ∑ t, (m t : ℝ) * BinaryCarrierMixedMenuWord.factorScale (sourceKind t) := by
  simp only [scale, Nat.cast_sum, Nat.cast_mul, factorScaleNat_cast]

theorem physicalDegree_eq (p : CriticalProfile) (m : Target → ℕ) :
    BinaryCarrierMixedProfile.physicalDegree points p m = 2 * p.rank + 8 * scale m := by
  unfold BinaryCarrierMixedProfile.physicalDegree
  rw [Fintype.sum_sum_type]
  change (∑ i, p.multiplicity i * Fintype.card (criticalActionPoints i)) +
      (∑ t, m t * Fintype.card (points t)) = 2 * p.rank + 8 * scale m
  rw [p.physical_degree]
  congr 1
  rw [scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [point_card]
  ring

theorem physicalDegree_real (p : CriticalProfile) (m : Target → ℕ) :
    (BinaryCarrierMixedProfile.physicalDegree points p m : ℝ) =
      2 * (p.rank : ℝ) + 8 * (scale m : ℝ) := by
  exact_mod_cast physicalDegree_eq p m

variable (m : Target → ℕ) {L : ℕ} (occurrences : Fin L ≃ (Σ t, Fin (m t)))

/-- An ordering of the original occurrences supplies a source position for
each one, even when several original colors share a master. -/
def occurrenceKinds : List BinaryCarrierMixedMenuWord.Kind :=
  List.ofFn (fun j => sourceKind (occurrences j).1)

@[simp] theorem occurrenceKinds_length : (occurrenceKinds m occurrences).length = L :=
  List.length_ofFn

theorem occurrenceWord_eq :
    BinaryCarrierMixedMenuWord.word (occurrenceKinds m occurrences) =
      BinaryCarrierOccurrenceWord.occurrenceWord sourceFactor m occurrences := by
  unfold BinaryCarrierMixedMenuWord.word occurrenceKinds
    BinaryCarrierOccurrenceWord.occurrenceWord
  rw [List.map_ofFn]
  rfl

/-- Enumerating original occurrences proves the scale identity without
counting distinct masters or numerical normal-profile labels. -/
theorem totalScale_occurrenceKinds :
    BinaryCarrierMixedMenuWord.totalScale (occurrenceKinds m occurrences) = (scale m : ℝ) := by
  rw [BinaryCarrierMixedMenuWord.totalScale_eq_sum, occurrenceKinds,
    List.map_ofFn, List.sum_ofFn]
  change (∑ j : Fin L, BinaryCarrierMixedMenuWord.factorScale
    (sourceKind (occurrences j).1)) = (scale m : ℝ)
  rw [occurrences.sum_comp
    (fun o : Σ t, Fin (m t) => BinaryCarrierMixedMenuWord.factorScale (sourceKind o.1)),
    Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (scale_cast m).symm

def occurrenceHistoryRows :
    CertifiedHistoryRows (BinaryCarrierOccurrenceWord.occurrenceWord sourceFactor m occurrences)
      (scale m : ℝ) := by
  rw [← occurrenceWord_eq m occurrences]
  simpa only [totalScale_occurrenceKinds] using
    BinaryCarrierMixedMenuWord.certifiedHistoryRows (occurrenceKinds m occurrences)

theorem occurrenceOrderBound :
    OrderBound (BinaryCarrierOccurrenceWord.occurrenceWord sourceFactor m occurrences) 12 := by
  rw [← occurrenceWord_eq m occurrences]
  exact BinaryCarrierMixedMenuWord.orderBound (occurrenceKinds m occurrences)

include occurrences in
/-- Count the literal original-action model. Its arbitrary original
predicate is retained through the fixed master inverse images. All source
order and history inputs are proved by the checked eight-master menu. -/
theorem modelFamily_card_le_reserve (p : CriticalProfile)
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints points p m)) → Prop) :
    (Nat.card (BinaryCarrierMixedProfile.ModelFamily points action p m P) : ℝ) ≤
      terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p)
        12 L (scale m : ℝ) :=
  BinaryCarrierMixedProfileEpimorphism.modelFamily_card_le_reserve
    points action sourceFactor hom hom_surjective p m occurrences
    12 (occurrenceOrderBound m occurrences) (scale m : ℝ)
      (occurrenceHistoryRows m occurrences) P

include occurrences in
/-- Original target normalizers and factorials remain indexed by the
twelve original physical colors. No source normalizer equality or bound
is assumed, and the entire critical product need not project fully. -/
theorem full_profile_card_le_reserve (p : CriticalProfile) {X : Type*}
    (labels : BinaryCarrierMixedProfile.ModelPoints points p m ≃ X) :
    (Nat.card (FullOrbitProfileOn (BinaryCarrierMixedProfile.points points)
      (BinaryCarrierMixedProfile.multiplicity p m)
      (BinaryCarrierMixedProfile.action points action) X) : ℝ) ≤
      ((2 * p.rank + 8 * scale m).factorial : ℝ) *
        terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p)
          12 L (scale m : ℝ) /
            BinaryCarrierMixedProfile.originalDenominator points action p m := by
  simpa only [physicalDegree_eq] using
    BinaryCarrierMixedProfileEpimorphism.full_profile_card_le_reserve
      points action sourceFactor hom hom_surjective p m occurrences
      12 (occurrenceOrderBound m occurrences) (scale m : ℝ)
        (occurrenceHistoryRows m occurrences) labels

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalActions
