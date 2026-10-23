import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepColumns
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientStepEntries

/-! The pilot's orthogonal-product entry is the actual E2*E4 entry.
The intermediate root is a single literal sum vector. No sum over the
general E6 root index set is evaluated in this proof. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientProductEntry
open CFSGFFourSerreMatrices CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6GeckDiagramCovariance CFSGNormTwoRootPairing CFSGIntegerMatrixPairing
open CFSGFFourE6NormQuotientStepEntries CFSGFFourE6NormQuotientCoefficientPilot
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

private theorem cartan_column (i j:Fin 6) :
    e6EZ i*ᵥPi.single (Sum.inl (E6Index j)) 1=
      |CartanMatrix.E₆ i j| • Pi.single (Sum.inr (E6Index i:Roots CartanMatrix.E₆)) 1 := by
  have h:=CFSGNormTwoGeckIntegralStepColumns.E_cartan_column CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index i) (E6Index j)
  have hc:=coordinate_cartan CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos i j
  change E6Base.cartanMatrix (E6Index i) (E6Index j)=CartanMatrix.E₆ i j at hc
  rw [hc] at h
  exact h

private theorem root_column (i:Fin 6) (j:Roots CartanMatrix.E₆) :
    e6EZ i*ᵥPi.single (Sum.inr j) 1=
      (if j.val= -simpleVector i then
        (Pi.single (Sum.inl (E6Index i)) (1:ℤ):GeckIndex→ℤ) else (0:GeckIndex→ℤ))+
        (if h:integerPairing CartanMatrix.E₆ (simpleVector i+j.val) (simpleVector i+j.val)=2 then
          (Pi.single (Sum.inr (⟨simpleVector i+j.val,h⟩:Roots CartanMatrix.E₆)) (1:ℤ):GeckIndex→ℤ)
            else (0:GeckIndex→ℤ)) := by
  have h:=CFSGNormTwoGeckIntegralStepColumns.E_root_column CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index i) j
  ext k
  have hk:=congrFun h k
  simpa only [E6Index_val,Pi.add_apply,Pi.zero_apply,ite_apply,dite_apply,Pi.single_apply] using hk

private theorem two_cartan_four_zero :
    e6EZ 2*ᵥPi.single (Sum.inl (E6Index 4)) 1=0 := by
  rw [cartan_column]
  have hc:|CartanMatrix.E₆ (2:Fin 6) 4|=0:=by decide +kernel
  rw [hc,zero_smul]

private theorem two_root_four_zero :
    e6EZ 2*ᵥPi.single (Sum.inr (E6Index 4:Roots CartanMatrix.E₆)) 1=0 := by
  have h:=root_column 2 (E6Index 4)
  have hn:simpleVector 4≠ -simpleVector 2:=by decide +kernel
  have hnorm:integerPairing CartanMatrix.E₆ (simpleVector 2+simpleVector 4)
      (simpleVector 2+simpleVector 4)≠2:=by decide +kernel
  simpa only [E6Index_val,if_neg hn,dif_neg hnorm,zero_add] using h

private theorem product_cartan_zero (j:Fin 6) :
    (e6EZ 2*e6EZ 4)*ᵥPi.single (Sum.inl (E6Index j)) 1=0 := by
  rw [←Matrix.mulVec_mulVec,cartan_column,Matrix.mulVec_smul,two_root_four_zero,smul_zero]

private theorem intermediate_ne_negative_two (s:Roots CartanMatrix.E₆) :
    simpleVector 4+s.val≠ -simpleVector 2 := by
  intro he
  have hs:s.val= -(simpleVector 2+simpleVector 4) := by
    funext j
    have hj:=congrFun he j
    change simpleVector 4 j+s.val j= -simpleVector 2 j at hj
    change s.val j= -(simpleVector 2 j+simpleVector 4 j)
    omega
  have hn:=s.property
  rw [hs] at hn
  have hc:integerPairing CartanMatrix.E₆ (-(simpleVector 2+simpleVector 4))
      (-(simpleVector 2+simpleVector 4))=4:=by decide +kernel
  rw [hc] at hn
  norm_num at hn

theorem e6EZ_orthogonal_product_entry (r s:GeckIndex) :
    (e6EZ 2*e6EZ 4) r s=orthogonalProductEntry 2 4 (eraseGeck r) (eraseGeck s) := by
  cases s with
  | inl s=>
    obtain ⟨j,rfl⟩:=E6Index.surjective s
    have h:=congrFun (product_cartan_zero j) r
    rw [Matrix.mulVec_single_one] at h
    change (e6EZ 2*e6EZ 4) r (Sum.inl (E6Index j))=0 at h
    cases r <;> simpa only [eraseGeck,orthogonalProductEntry,Pi.zero_apply] using h
  | inr s=>
    have hcol : (e6EZ 2*e6EZ 4)*ᵥPi.single (Sum.inr s) 1=
        e6EZ 2*ᵥ(if h:integerPairing CartanMatrix.E₆ (simpleVector 4+s.val)
          (simpleVector 4+s.val)=2 then
            (Pi.single (Sum.inr (⟨simpleVector 4+s.val,h⟩:Roots CartanMatrix.E₆)) (1:ℤ):GeckIndex→ℤ)
              else (0:GeckIndex→ℤ)) := by
      rw [←Matrix.mulVec_mulVec,root_column,Matrix.mulVec_add]
      have hz:e6EZ 2*ᵥ(if s.val= -simpleVector 4 then
          (Pi.single (Sum.inl (E6Index 4)) (1:ℤ):GeckIndex→ℤ) else (0:GeckIndex→ℤ))=0 := by
        split_ifs
        · exact two_cartan_four_zero
        · exact Matrix.mulVec_zero _
      rw [hz,zero_add]
    have h:=congrFun hcol r
    rw [Matrix.mulVec_single_one] at h
    change (e6EZ 2*e6EZ 4) r (Sum.inr s)=_ at h
    by_cases hnorm:integerPairing CartanMatrix.E₆ (simpleVector 4+s.val) (simpleVector 4+s.val)=2
    · simp only [dif_pos hnorm,Matrix.mulVec_single_one] at h
      change (e6EZ 2*e6EZ 4) r (Sum.inr s)=
        e6EZ 2 r (Sum.inr (⟨simpleVector 4+s.val,hnorm⟩:Roots CartanMatrix.E₆)) at h
      rw [h,e6EZ_entry]
      cases r with
      | inl r=>
        simp only [eraseGeck,stepEntry,orthogonalProductEntry,
          intermediate_ne_negative_two s,and_false,if_false]
      | inr r=>
        simp only [eraseGeck,stepEntry,orthogonalProductEntry,hnorm,true_and]
    · simp only [dif_neg hnorm,Matrix.mulVec_zero,Pi.zero_apply] at h
      rw [h]
      cases r <;> simp only [eraseGeck,orthogonalProductEntry,hnorm,false_and,if_false]

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientProductEntry
