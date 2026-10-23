import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepEntries

/-! Sparse integral columns for a simply-laced Geck raising operator.
The only possible root output is the literal sum vector of norm two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralStepEntries
variable {n:Type*} [Fintype n] [DecidableEq n]
    (A:Matrix n n ℤ) (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b:(rootPairing A hs hp).Base)

theorem E_cartan_column (i j:b.support) :
    CFSGGeckIntegralMatrices.E b i*ᵥPi.single (Sum.inl j) 1=
      |b.cartanMatrix i j| • Pi.single (Sum.inr (i:Roots A)) 1 := by
  rw [Matrix.mulVec_single_one]
  ext (k|k)
  · change CFSGGeckIntegralMatrices.E b i (Sum.inl k) (Sum.inl j)=_
    simp only [E_inl_inl A hs hp b,Pi.smul_apply,Pi.single_apply,Sum.inl_ne_inr,
      if_false,smul_zero]
  · change CFSGGeckIntegralMatrices.E b i (Sum.inr k) (Sum.inl j)=_
    rw [E_inr_inl A hs hp b]
    simp only [Pi.smul_apply,Pi.single_apply,Sum.inr.injEq,smul_eq_mul,mul_ite,mul_one,mul_zero]
    have he:k.val=(i:Roots A).val ↔ k=(i:Roots A):=Subtype.ext_iff.symm
    simp only [he]

theorem E_root_column (i:b.support) (j:Roots A) :
    CFSGGeckIntegralMatrices.E b i*ᵥPi.single (Sum.inr j) 1=
      (if j.val= -(i:Roots A).val then
        (Pi.single (Sum.inl i) (1:ℤ):b.support⊕Roots A→ℤ) else (0:b.support⊕Roots A→ℤ))+
        (if h:integerPairing A ((i:Roots A).val+j.val) ((i:Roots A).val+j.val)=2 then
          (Pi.single (Sum.inr (⟨(i:Roots A).val+j.val,h⟩:Roots A)) (1:ℤ):b.support⊕Roots A→ℤ)
            else (0:b.support⊕Roots A→ℤ)) := by
  rw [Matrix.mulVec_single_one]
  by_cases hn:j.val= -(i:Roots A).val
  · have hz:(i:Roots A).val+j.val=0:=by rw [hn,add_neg_cancel]
    have hnorm:integerPairing A ((i:Roots A).val+j.val) ((i:Roots A).val+j.val)≠2 := by
      simp only [hz,map_zero]
      decide
    simp only [if_pos hn,dif_neg hnorm]
    ext (k|k)
    · change CFSGGeckIntegralMatrices.E b i (Sum.inl k) (Sum.inr j)=
        (Pi.single (Sum.inl i) (1:ℤ):b.support⊕Roots A→ℤ) (Sum.inl k)+0
      simp only [E_inl_inr A hs hp b,hn,and_true,Pi.single_apply,Sum.inl.injEq,add_zero]
    · change CFSGGeckIntegralMatrices.E b i (Sum.inr k) (Sum.inr j)=
        (Pi.single (Sum.inl i) (1:ℤ):b.support⊕Roots A→ℤ) (Sum.inr k)+0
      have hk:k.val≠(i:Roots A).val+j.val := by
        intro he
        have hh:=k.property
        rw [he,hz,map_zero] at hh
        norm_num at hh
      simp only [E_inr_inr A hs hp b,if_neg hk,Pi.single_apply,Sum.inr_ne_inl,if_false,add_zero]
  · simp only [if_neg hn]
    by_cases hsum:integerPairing A ((i:Roots A).val+j.val) ((i:Roots A).val+j.val)=2
    · simp only [dif_pos hsum]
      ext (k|k)
      · change CFSGGeckIntegralMatrices.E b i (Sum.inl k) (Sum.inr j)=
          (Pi.single (Sum.inr (⟨(i:Roots A).val+j.val,hsum⟩:Roots A)) (1:ℤ):b.support⊕Roots A→ℤ) (Sum.inl k)
        simp only [E_inl_inr A hs hp b,hn,and_false,if_false,Pi.single_apply,Sum.inl_ne_inr,zero_add]
      · rw [_root_.zero_add]
        change CFSGGeckIntegralMatrices.E b i (Sum.inr k) (Sum.inr j)=
          (Pi.single (Sum.inr (⟨(i:Roots A).val+j.val,hsum⟩:Roots A)) (1:ℤ):b.support⊕Roots A→ℤ) (Sum.inr k)
        simp only [E_inr_inr A hs hp b,Pi.single_apply,Sum.inr.injEq,zero_add]
        have he:k.val=(i:Roots A).val+j.val ↔ k=(⟨(i:Roots A).val+j.val,hsum⟩:Roots A):=
          ⟨fun h=>Subtype.ext h,fun h=>congrArg (fun r:Roots A=>r.val) h⟩
        simp only [he]
    · simp only [dif_neg hsum]
      ext (k|k)
      · change CFSGGeckIntegralMatrices.E b i (Sum.inl k) (Sum.inr j)=0
        simp only [E_inl_inr A hs hp b,hn,and_false,if_false]
      · change CFSGGeckIntegralMatrices.E b i (Sum.inr k) (Sum.inr j)=0
        have hk:k.val≠(i:Roots A).val+j.val := by
          intro he
          apply hsum
          rw [←he]
          exact k.property
        simp only [E_inr_inr A hs hp b,if_neg hk]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepColumns
