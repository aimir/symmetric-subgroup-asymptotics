import SymmetricSubgroupAsymptotics.BinaryCarrierWordHistory
import SymmetricSubgroupAsymptotics.BinaryCarrierAbelianQuotient
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionImage
import SymmetricSubgroupAsymptotics.PrimeEvaluationKernelOrder
import SymmetricSubgroupAsymptotics.JointCapacityRowEnvelope
import Lean.Elab.Tactic.Omega

/-! Exact original quotient fields for the entire above-derived branch.
The only head estimate supplied by the data is an actual original-group
theorem, separately from the proved order and quotient transports. The
normal subgroup and its ambient conjugation are retained in every field.
No numerical normal menu, weights or global coverage is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierAboveDerivedRows

open FullSubdirectGoursat BinaryMarkedGoursatPeel JointCapacityRow

def imageDimension {G : Type*} [Group G] [Finite G] (N : Subgroup G) : ℕ :=
  Module.finrank (ZMod 2) (primeDerivedImage 2 N)

def row (d s e w : ℕ) : JointCapacityRow :=
  ⟨max e w, d + w, e, e, (s - w : ℕ), 0⟩

/-- Every field refers to the same actual factor. Concrete applications
must prove these original-group facts, rather than supply catalogue labels. -/
structure Data (A : BinaryCarrierWord.Factor) (d s e : ℕ) : Prop where
  kernel : (primeAbelianizationGroupMap 2 A.Carrier).ker = commutator A.Carrier
  derivedCard : Nat.card (commutator A.Carrier) = 2 ^ d
  evaluationRank : Module.finrank (ZMod 2) (PrimeAbelianization 2 A.Carrier) = s
  derivedRank : primeDerivedNormalRank 2 A.Carrier = e
  head_bound : ∀ (N : Subgroup A.Carrier) [N.Normal], commutator A.Carrier ≤ N →
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ max e (imageDimension N)

namespace Data

variable {A : BinaryCarrierWord.Factor} {d s e : ℕ} (C : Data A d s e)
include C

theorem imageDimension_le (N : Subgroup A.Carrier) : imageDimension N ≤ s :=
  (Submodule.finrank_le (primeDerivedImage 2 N)).trans_eq C.evaluationRank

theorem original_card : Nat.card A.Carrier = 2 ^ (d + s) := by
  have hc : Module.finrank (ZMod 2) (PrimeCharacters 2 A.Carrier) = s := by
    simpa only [PrimeAbelianization, Subspace.dual_finrank_eq] using C.evaluationRank
  rw [card_eq_prime_pow_of_evaluationKernel_eq 2 C.kernel d C.derivedCard, hc, Nat.add_comm]

theorem normal_card (N : Subgroup A.Carrier) [N.Normal]
    (hDN : commutator A.Carrier ≤ N) : Nat.card N = 2 ^ (d + imageDimension N) := by
  have h := primeDerivedImage_pow_finrank_mul_intersection 2 C.kernel N
  rw [inf_eq_right.mpr hDN, C.derivedCard] at h
  change 2 ^ imageDimension N * 2 ^ d = Nat.card N at h
  rw [pow_add, Nat.mul_comm]
  exact h.symm

theorem quotient_card (N : Subgroup A.Carrier) [N.Normal]
    (hDN : commutator A.Carrier ≤ N) :
    Nat.card (A.Carrier ⧸ N) = 2 ^ (s - imageDimension N) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [C.original_card, C.normal_card N hDN] at h
  apply Nat.eq_of_mul_eq_mul_right
    (pow_pos (by decide : 0 < (2 : ℕ)) (d + imageDimension N))
  calc
    _ = 2 ^ (d + s) := h.symm
    _ = 2 ^ (s - imageDimension N) * 2 ^ (d + imageDimension N) := by
      rw [← pow_add]
      congr 1
      have hw := C.imageDimension_le N
      omega

theorem orderLog_eq (N : NormalAxis A.Carrier) (hDN : commutator A.Carrier ≤ N.1) :
    orderLog N = d + imageDimension N.1 := by
  change Nat.log 2 (Nat.card N.1) = _
  rw [C.normal_card N.1 hDN, Nat.log_pow (by decide)]

theorem centerSlope_eq (N : NormalAxis A.Carrier) (hDN : commutator A.Carrier ≤ N.1) :
    centerSlope N = s - imageDimension N.1 := by
  rw [centerSlope_eq_log_quotient_of_commutator_le N hDN,
    C.quotient_card N.1 hDN, Nat.log_pow (by decide)]

theorem derivedHead_eq (N : NormalAxis A.Carrier) (hDN : commutator A.Carrier ≤ N.1) :
    derivedHead N = e :=
  (derivedHead_eq_of_commutator_le N hDN).trans C.derivedRank

/-- The actual row's order and two quotient slopes are exact. Only its
head and radical-head entries are majorized, on that same original N. -/
theorem actualRow_boundedBy (N : NormalAxis A.Carrier) (hDN : commutator A.Carrier ≤ N.1) :
    BoundedBy (BinaryCarrierWord.actualRow (A := A) N) (row d s e (imageDimension N.1)) := by
  have ha := radicalHead_le_derivedHead_of_evaluation_kernel_le N C.kernel.le
  refine ⟨C.head_bound N.1 hDN, (C.orderLog_eq N hDN).le,
    (C.derivedHead_eq N hDN).le, ha.trans (C.derivedHead_eq N hDN).le, ?_, ?_⟩
  · change (centerSlope N : ℝ) ≤ ((s - imageDimension N.1 : ℕ) : ℝ)
    exact Nat.cast_le.mpr (C.centerSlope_eq N hDN).le
  · change (derivedSlope N : ℝ) ≤ 0
    rw [derivedSlope_eq_zero_of_commutator_le N hDN]
    simp only [Nat.cast_zero, le_refl]

end Data
end SymmetricSubgroupAsymptotics.BinaryCarrierAboveDerivedRows
