import SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenu
import SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenuEnergy
import SymmetricSubgroupAsymptotics.BinaryCarrierWordEffectiveEnvelope

/-! Envelope choices are made separately at every position of every
original normal history. Repeated factors and repeated numerical labels
never identify positions or normal axes. The resulting certificates leave
all original axis weights explicit. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenuHistory

open FullSubdirectGoursat BinaryCarrierWord BinaryCarrierMasterMenu
open JointCapacityRow

def CoveredFactor (A : Factor) : Prop :=
  ∀ N : NormalAxis A.Carrier,
    ∃ label : Label, (actualRow (A := A) N).EffectivelyBoundedBy (envelope label)

def CoveredWord (w : List Factor) : Prop := ∀ A ∈ w, CoveredFactor A

/-- Coverage follows the original list and normal-axis history, not a
list of distinct factors or a set of numerical labels. -/
theorem rows_covered (w : List Factor) : ∀ (hc : CoveredWord w)
    (h : History w) (i : Fin w.length),
    ∃ label : Label, (rows h i).EffectivelyBoundedBy (envelope label) := by
  induction w with
  | nil => intro hc h i; exact Fin.elim0 i
  | cons A w ih =>
      intro hc h i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hc A (by simp) h.1
      · exact ih (fun B hB => hc B (List.mem_cons_of_mem A hB)) h.2 j

/-- A choice for each literal position; no injectivity or multiplicity
bound for this label function is asserted. -/
def labels (w : List Factor) (hc : CoveredWord w)
    (h : History w) (i : Fin w.length) : Label :=
  Classical.choose (rows_covered w hc h i)

theorem labels_bound (w : List Factor) (hc : CoveredWord w)
    (h : History w) (i : Fin w.length) :
    (rows h i).EffectivelyBoundedBy (envelope (labels w hc h i)) :=
  Classical.choose_spec (rows_covered w hc h i)

/-- The scale corresponding to mass eight at each original position. -/
def totalScale (w : List Factor) : ℝ := 2 * (w.length : ℝ)

/-- The proved scalar menu supplies all color and pair obligations.
Every original position contributes mass eight, including repetitions. -/
def certifiedHistoryRows (w : List Factor) (hc : CoveredWord w) :
    CertifiedHistoryRows w (totalScale w) :=
  CertifiedHistoryRows.of_effectiveUpperRows w (totalScale w)
    (fun h i => envelope (labels w hc h i))
    (labels_bound w hc)
    (fun h i => BinaryCarrierMasterMenuEnergy.color (labels w hc h i))
    (fun _ _ => 8)
    (fun _ _ => by norm_num)
    (fun h i => BinaryCarrierMasterMenuEnergy.head_le (labels w hc h i))
    (fun h i => BinaryCarrierMasterMenuEnergy.second_le (labels w hc h i))
    (fun h a i _ => BinaryCarrierMasterMenuEnergy.pair_le
      (labels w hc h a) (labels w hc h i))
    (by
      intro h
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        totalScale]
      ring)

/-- The sum still ranges over all original histories with their actual
weights. The number of envelope labels does not enter its prefactor. -/
theorem normalHistorySum_le_reserve (w : List Factor) (hc : CoveredWord w)
    (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2) :
    (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) * normalHistorySum w v (j-ell) 0 ell ≤
      axisWeightProduct w v *
        (2 : ℝ)^((R+4*totalScale w)^2/4 -
          (25/82)*R*totalScale w - (29/164)*(totalScale w)^2) :=
  BinaryCarrierWord.normalHistorySum_le_reserve w v hv (totalScale w)
    (certifiedHistoryRows w hc) R j ell hj hell

/-- The existing whole-word marked bound applies with its actual normal
weight product and a separately supplied original factor-order bound. -/
theorem markedSum_le_reserve (w : List Factor) (hc : CoveredWord w)
    (b : ℕ) (hb : OrderBound w b) (v : AxisWeights w) (hv : WeightsNonnegative w v)
    (P : Subgroup (Product w) → Prop)
    (R j ell : ℝ) (hj : 0 ≤ j ∧ j ≤ R) (hell : 0 ≤ ell ∧ ell ≤ R/2) :
    (2 : ℝ)^(ell*(R/2-ell)+(j-ell)*(R-j)) * markedSum w v P (j-ell) 0 ell ≤
      (((binaryStructuredOrderConstant b *
        (b*w.length+2)^(binaryStructuredOrderConstant b) : ℕ) : ℝ)^w.length) *
        axisWeightProduct w v *
          (2 : ℝ)^((R+4*totalScale w)^2/4 -
            (25/82)*R*totalScale w - (29/164)*(totalScale w)^2) :=
  BinaryCarrierWord.markedSum_le_reserve_of_orderBound w b hb v hv P (totalScale w)
    (certifiedHistoryRows w hc) R j ell hj hell

end SymmetricSubgroupAsymptotics.BinaryCarrierMasterMenuHistory
