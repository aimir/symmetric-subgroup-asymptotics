import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentWeyl
import SymmetricSubgroupAsymptotics.CFSGTwistedA2OriginalSylow

/-! Two actual conjugate original unipotent subgroups already contain
the chosen original Weyl word and lie in the original derived subgroup.
No claim of whole-source generation is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
open CFSGTwistedA2HighestRootUnits CFSGSerreOrdinaryTwists
variable (K : Type) [Field K]

theorem highest_eq_upperNatural (σ : K ≃+* K) (t : K) :
    highest K t = upperNatural K σ 0 t := by
  apply Subtype.ext
  apply Units.ext
  rw [highest_array, upperNatural_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperArray, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem highest_norm (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) : NormCondition (definingFieldAutomorphism q 2) 0 t := by
  change t + t ^ q.order = 0 * definingFieldAutomorphism q 2 0
  rw [ht]
  simp

theorem highestFixed_mem_unipotent (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) : highestFixed q t ht ∈ originalUnipotent q := by
  let v : naturalUnipotent q := ⟨highest (q.Extension 2) t,
    0, t, highest_norm q t ht, highest_eq_upperNatural _ _ t⟩
  exact ⟨v, rfl⟩

theorem weyl_conjugate_highest (t : K) (ht : t ≠ 0) :
    weylNatural K t * highest K t * (weylNatural K t)⁻¹ = opposite K (-t⁻¹) := by
  have h : weylNatural K t * highest K t = opposite K (-t⁻¹) * weylNatural K t := by
    apply Subtype.ext
    apply Units.ext
    change ((weylNatural K t).val : Mat K 2) * ((highest K t).val : Mat K 2) =
      ((opposite K (-t⁻¹)).val : Mat K 2) * ((weylNatural K t).val : Mat K 2)
    simp only [weylNatural_array K t ht, highest_array, opposite_array]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem originalWeyl_conjugate_highest (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht0 : t ≠ 0) (ht : t ^ q.order = -t) :
    originalWeyl q t ht * highestFixed q t ht * (originalWeyl q t ht)⁻¹ =
      oppositeFixed q (-t⁻¹) (neg_inv_skew q t ht) := by
  apply fixedToModel_injective q
  simp only [map_mul, map_inv]
  change elementaryToModel (q.Extension 2) (weylNatural (q.Extension 2) t) *
      elementaryToModel (q.Extension 2) (highest (q.Extension 2) t) *
        (elementaryToModel (q.Extension 2) (weylNatural (q.Extension 2) t))⁻¹ =
      elementaryToModel (q.Extension 2) (opposite (q.Extension 2) (-t⁻¹))
  rw [← map_inv, ← map_mul, ← map_mul, weyl_conjugate_highest _ t ht0]

def oppositeOriginalUnipotent (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) : Subgroup (OriginalFixedA 2 q) :=
  (originalUnipotent q).map (MulAut.conj (originalWeyl q t ht)).toMonoidHom

def rootGenerated (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht : t ^ q.order = -t) : Subgroup (OriginalFixedA 2 q) :=
  originalUnipotent q ⊔ oppositeOriginalUnipotent q t ht

theorem originalWeyl_mem_rootGenerated (q : CFSG.PrimePower) (t : q.Extension 2)
    (ht0 : t ≠ 0) (ht : t ^ q.order = -t) :
    originalWeyl q t ht ∈ rootGenerated q t ht := by
  have hu := highestFixed_mem_unipotent q t ht
  have hm : oppositeFixed q (-t⁻¹) (neg_inv_skew q t ht) ∈
      oppositeOriginalUnipotent q t ht :=
    ⟨highestFixed q t ht, hu, originalWeyl_conjugate_highest q t ht0 ht⟩
  have hule : originalUnipotent q ≤ rootGenerated q t ht := le_sup_left
  have hole : oppositeOriginalUnipotent q t ht ≤ rootGenerated q t ht := le_sup_right
  rw [originalWeyl_word]
  exact (rootGenerated q t ht).mul_mem
    ((rootGenerated q t ht).mul_mem (hule hu) (hole hm)) (hule hu)

theorem rootGenerated_le_commutator (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (t : q.Extension 2) (ht : t ^ q.order = -t) :
    rootGenerated q t ht ≤ commutator (OriginalFixedA 2 q) := by
  apply sup_le (originalUnipotent_le_commutator q hq)
  rintro g ⟨x, hx, rfl⟩
  exact (inferInstance : (commutator (OriginalFixedA 2 q)).Normal).conj_mem
    x (originalUnipotent_le_commutator q hq hx) (originalWeyl q t ht)

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
