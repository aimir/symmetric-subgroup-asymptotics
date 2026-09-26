import SymmetricSubgroupAsymptotics.BinaryCarrierStarCrossing16T1332
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalDerivedHead
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionImage
import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierStarEnvelope

/-! Actual crossing rows of the original 16T1332 action. Both dimensions
come from the same literal normal subgroup. The head and second heads
are upper bounds; the order and quotient slopes are exact. No normal
enumeration, row realization, weight, or owner coverage is asserted. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierStarCrossingRows16T1332

open FullSubdirectGoursat BinaryMarkedGoursatPeel JointCapacityRow

abbrev Original := BinaryCarrierStarCrossing16T1332.Original

def factor : BinaryCarrierWord.Factor where
  Carrier := Original
  group := inferInstance
  finite := inferInstance
  binary := BinaryCarrierExactOrder16T1332.original_isPGroup

/-- The full space of original derived characters vanishing on N∩G′. -/
def parameterDimension (N : Subgroup Original) : ℕ :=
  Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 (N ⊓ commutator Original))

/-- The image of the same original N in the actual evaluation quotient. -/
def imageDimension (N : Subgroup Original) : ℕ :=
  Module.finrank (ZMod 2) (primeDerivedImage 2 N)

def row (ell w : ℕ) : JointCapacityRow :=
  ⟨4 - ell, 6 - ell + w, max 2 (4 - ell), max 2 (4 - ell), (4 - w : ℕ), ell⟩

theorem dimensions (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    1 ≤ parameterDimension N ∧ 1 ≤ imageDimension N ∧
      parameterDimension N + imageDimension N ≤ 4 := by
  have hsum := BinaryCarrierStarCrossing16T1332.image_add_vanishing_le_four N hnotDN
  change imageDimension N + parameterDimension N ≤ 4 at hsum
  exact ⟨BinaryCarrierStarCrossing16T1332.vanishing_one_le N hnotDN,
    BinaryCarrierStarCrossing16T1332.image_one_le N hnotND, by omega⟩

/-- The order of the original derived intersection, without a supplied
order label or a list of possible intersections. -/
theorem intersection_card (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Nat.card ↥(N ⊓ commutator Original) = 2 ^ (6 - parameterDimension N) := by
  have hdim := dimensions N hnotND hnotDN
  have hell : parameterDimension N ≤ 6 := by omega
  have h := quotientCommutator_card_mul_inf N
  rw [BinaryCarrierStarCrossing16T1332.quotient_derived_card N hnotND hnotDN,
    BinaryCarrierDerivedOrder16T1332.card_commutator] at h
  change 2 ^ parameterDimension N * Nat.card ↥(N ⊓ commutator Original) = 64 at h
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) (parameterDimension N))
  rw [← Nat.pow_add, Nat.add_sub_of_le hell]
  exact h

theorem normal_card (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Nat.card N = 2 ^ (6 - parameterDimension N + imageDimension N) := by
  have h := primeDerivedImage_pow_finrank_mul_intersection 2
    BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator N
  rw [intersection_card N hnotND hnotDN] at h
  change 2 ^ imageDimension N * 2 ^ (6 - parameterDimension N) = Nat.card N at h
  rw [Nat.pow_add, Nat.mul_comm]
  exact h.symm

theorem orderLog_eq (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    orderLog N = 6 - parameterDimension N.1 + imageDimension N.1 := by
  change Nat.log 2 (Nat.card N.1) = _
  rw [normal_card N.1 hnotND hnotDN, Nat.log_pow (by decide)]

theorem centerSlope_eq (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    centerSlope N = 4 - imageDimension N.1 := by
  change Nat.log 2 (Nat.card (Subgroup.center (Original ⧸ N.1))) =
    4 - Module.finrank (ZMod 2) (primeDerivedImage 2 N.1)
  rw [BinaryCarrierStarCrossing16T1332.quotient_center_card N.1 hnotND hnotDN,
    Nat.log_pow (by decide)]

theorem derivedSlope_eq (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    derivedSlope N = parameterDimension N.1 := by
  change Nat.log 2 (Nat.card (commutator (Original ⧸ N.1))) =
    Module.finrank (ZMod 2) (derivedCharactersVanishingOn 2 (N.1 ⊓ commutator Original))
  rw [BinaryCarrierStarCrossing16T1332.quotient_derived_card N.1 hnotND hnotDN,
    Nat.log_pow (by decide)]

/-- Each of the six bounds is on the same original normal axis. Powers
can improve the head; equality of that head with its envelope is not claimed. -/
theorem actualRow_boundedBy (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
      (row (parameterDimension N.1) (imageDimension N.1)) := by
  have hk := BinaryCarrierStarCrossing16T1332.head_add_vanishing_le_four N.1 hnotND hnotDN
  change head N + parameterDimension N.1 ≤ 4 at hk
  have hm := BinaryCarrierStarCrossing16T1332.normalHeadMax_intersection_le N.1 hnotND hnotDN
  change derivedHead N ≤ max 2 (4 - parameterDimension N.1) at hm
  have ha := primeRelativeRadical_head_le_axis_max_of_evaluation_kernel_le 2 N.1
    BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator.le
  change radicalHead N ≤ derivedHead N at ha
  refine ⟨?_, ?_, hm, ha.trans hm, ?_, ?_⟩
  · change head N ≤ 4 - parameterDimension N.1
    omega
  · exact (orderLog_eq N hnotND hnotDN).le
  · change (centerSlope N : ℝ) ≤ ((4 - imageDimension N.1 : ℕ) : ℝ)
    exact Nat.cast_le.mpr (centerSlope_eq N hnotND hnotDN).le
  · change (derivedSlope N : ℝ) ≤ (parameterDimension N.1 : ℝ)
    exact Nat.cast_le.mpr (derivedSlope_eq N hnotND hnotDN).le

theorem row_boundedBy_coarse (ell w : ℕ)
    (hell : 1 ≤ ell) (hw : 1 ≤ w) (hsum : ell + w ≤ 4) :
    BoundedBy (row ell w) BinaryCarrierStarEnvelope.coarseEnvelope := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 4 - ell ≤ 3
    omega
  · change 6 - ell + w ≤ 8
    omega
  · change max 2 (4 - ell) ≤ 3
    exact max_le (by decide) (by omega)
  · change max 2 (4 - ell) ≤ 3
    exact max_le (by decide) (by omega)
  · change ((4 - w : ℕ) : ℝ) ≤ 3
    exact_mod_cast (show 4 - w ≤ 3 by omega)
  · change (ell : ℝ) ≤ 3
    exact_mod_cast (show ell ≤ 3 by omega)

/-- A single proved upper box covers every actual crossing normal of
this original master; normal identities and weights remain distinct. -/
theorem actualRow_boundedBy_coarse (N : NormalAxis Original)
    (hnotND : ¬N.1 ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := factor) N)
      BinaryCarrierStarEnvelope.coarseEnvelope := by
  have h := actualRow_boundedBy N hnotND hnotDN
  have hd := dimensions N.1 hnotND hnotDN
  have hc := row_boundedBy_coarse (parameterDimension N.1) (imageDimension N.1)
    hd.1 hd.2.1 hd.2.2
  exact ⟨h.head.trans hc.head, h.order.trans hc.order,
    h.derivedHead.trans hc.derivedHead, h.radicalHead.trans hc.radicalHead,
    h.center.trans hc.center, h.derived.trans hc.derived⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierStarCrossingRows16T1332
