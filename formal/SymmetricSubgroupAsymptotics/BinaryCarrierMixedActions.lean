import SymmetricSubgroupAsymptotics.BinaryCarrierMixedMenuReserve
import SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile

/-! The literal eight- and sixteen-point actions behind the mixed word.
The actual occurrence word receives its proved history certificate and
order bound. Physical degree is exactly2R+8T, while original normalizer
orders and occurrence factorials remain untouched. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions

open BinaryCarrierWord BinaryCarrierMixedMenuWord

def points : Kind → Type
  | .x => Fin 8
  | .j => Fin 8
  | .p => Fin 8
  | .degree16 _ => Fin 16

instance (k : Kind) : Fintype (points k) := by
  cases k <;> dsimp [points] <;> infer_instance

instance (k : Kind) : Nonempty (points k) := by
  cases k <;> dsimp [points] <;> infer_instance

/-- Original generator tuples, in their existing literal order. -/
def action : (k : Kind) → Subgroup (Equiv.Perm (points k))
  | .x => Subgroup.closure (Set.range BinaryMenuCayley8T26.generators)
  | .j => Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)
  | .p => Subgroup.closure (Set.range BinaryMenuCayley8T35.generators)
  | .degree16 .t1082 => Subgroup.closure (Set.range BinaryActionData16.node1082Generators)
  | .degree16 .t1083 => Subgroup.closure (Set.range BinaryActionData16.node1083Generators)
  | .degree16 .t1084 => Subgroup.closure (Set.range BinaryActionData16.node1084Generators)
  | .degree16 .t1332 => Subgroup.closure (Set.range BinaryActionData16.node1332Generators)
  | .degree16 .t1547 => Subgroup.closure (Set.range BinaryActionData16.node1547Generators)

theorem action_binary (k : Kind) : IsPGroup 2 (action k) := by
  cases k with
  | x => exact (factor Kind.x).binary
  | j => exact (factor Kind.j).binary
  | p => exact (factor Kind.p).binary
  | degree16 m =>
      cases m with
      | t1082 => exact (factor (.degree16 .t1082)).binary
      | t1083 => exact (factor (.degree16 .t1083)).binary
      | t1084 => exact (factor (.degree16 .t1084)).binary
      | t1332 => exact (factor (.degree16 .t1332)).binary
      | t1547 => exact (factor (.degree16 .t1547)).binary

/-- Equality of the complete Factor, not merely an abstract group isomorphism. -/
theorem localFactor_eq (k : Kind) :
    BinaryCarrierMixedProfile.localFactor points action action_binary k = factor k := by
  cases k with
  | x => rfl
  | j => rfl
  | p => rfl
  | degree16 m => cases m <;> rfl

def factorScaleNat : Kind → ℕ
  | .x => 1
  | .j => 1
  | .p => 1
  | .degree16 _ => 2

theorem factorScaleNat_cast (k : Kind) : (factorScaleNat k : ℝ) = factorScale k := by
  cases k <;> norm_num [factorScaleNat, factorScale]

theorem point_card (k : Kind) : Fintype.card (points k) = 8 * factorScaleNat k := by
  cases k <;> rfl

/-- Count every original occurrence, with scale1 for X/J/P and scale2 for each degree-sixteen master. -/
def scale (m : Kind → ℕ) : ℕ := ∑ k, m k * factorScaleNat k

theorem scale_cast (m : Kind → ℕ) :
    (scale m : ℝ) = ∑ k, (m k : ℝ) * factorScale k := by
  simp only [scale, Nat.cast_sum, Nat.cast_mul, factorScaleNat_cast]

theorem physicalDegree_eq (p : CriticalProfile) (m : Kind → ℕ) :
    BinaryCarrierMixedProfile.physicalDegree points p m = 2 * p.rank + 8 * scale m := by
  unfold BinaryCarrierMixedProfile.physicalDegree
  rw [Fintype.sum_sum_type]
  change (∑ i, p.multiplicity i * Fintype.card (criticalActionPoints i)) +
      (∑ k, m k * Fintype.card (points k)) = 2 * p.rank + 8 * scale m
  rw [p.physical_degree]
  congr 1
  rw [scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [point_card]
  ring

theorem physicalDegree_real (p : CriticalProfile) (m : Kind → ℕ) :
    (BinaryCarrierMixedProfile.physicalDegree points p m : ℝ) =
      2 * (p.rank : ℝ) + 8 * (scale m : ℝ) := by
  exact_mod_cast physicalDegree_eq p m

variable (m : Kind → ℕ) {L : ℕ} (occurrences : Fin L ≃ (Σ k, Fin (m k)))

/-- Any explicit original-occurrence ordering gives exactly this literal word. -/
def occurrenceKinds : List Kind := List.ofFn (fun j => (occurrences j).1)

@[simp] theorem occurrenceKinds_length : (occurrenceKinds m occurrences).length = L :=
  List.length_ofFn

theorem occurrenceWord_eq :
    word (occurrenceKinds m occurrences) =
      BinaryCarrierOccurrenceWord.occurrenceWord
        (BinaryCarrierMixedProfile.localFactor points action action_binary) m occurrences := by
  unfold word occurrenceKinds BinaryCarrierOccurrenceWord.occurrenceWord
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact (localFactor_eq (occurrences j).1).symm

/-- The sum is independent of the chosen ordering and of every normal-axis
choice, because the equivalence enumerates each original occurrence once. -/
theorem totalScale_occurrenceKinds :
    totalScale (occurrenceKinds m occurrences) = (scale m : ℝ) := by
  rw [totalScale_eq_sum, occurrenceKinds, List.map_ofFn, List.sum_ofFn]
  change (∑ j : Fin L, factorScale (occurrences j).1) = (scale m : ℝ)
  rw [occurrences.sum_comp (fun o : Σ k, Fin (m k) => factorScale o.1),
    Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact (scale_cast m).symm

def occurrenceHistoryRows :
    CertifiedHistoryRows
      (BinaryCarrierOccurrenceWord.occurrenceWord
        (BinaryCarrierMixedProfile.localFactor points action action_binary) m occurrences)
      (scale m : ℝ) := by
  rw [← occurrenceWord_eq m occurrences]
  simpa only [totalScale_occurrenceKinds] using
    certifiedHistoryRows (occurrenceKinds m occurrences)

theorem occurrenceOrderBound :
    OrderBound
      (BinaryCarrierOccurrenceWord.occurrenceWord
        (BinaryCarrierMixedProfile.localFactor points action action_binary) m occurrences) 12 := by
  rw [← occurrenceWord_eq m occurrences]
  exact orderBound (occurrenceKinds m occurrences)

include occurrences in
/-- This is the literal original-action model, with an arbitrary predicate
on its complete permutation subgroup. No supplied model-count bound remains. -/
theorem modelFamily_card_le_reserve (p : CriticalProfile)
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints points p m)) → Prop) :
    (Nat.card (BinaryCarrierMixedProfile.ModelFamily points action p m P) : ℝ) ≤
      terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p)
        12 L (scale m : ℝ) :=
  BinaryCarrierMixedProfile.modelFamily_card_le_reserve points action action_binary
    p m occurrences 12 (occurrenceOrderBound m occurrences) (scale m : ℝ)
      (occurrenceHistoryRows m occurrences) P

include occurrences in
/-- Original physical normalizers and occurrence factorials are retained by
the generic upper assembly. There is no replacement by automorphism orders. -/
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
    BinaryCarrierMixedProfile.full_profile_card_le_reserve points action action_binary
      p m occurrences 12 (occurrenceOrderBound m occurrences) (scale m : ℝ)
        (occurrenceHistoryRows m occurrences) labels

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedActions
