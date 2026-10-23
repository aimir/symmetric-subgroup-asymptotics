import SymmetricSubgroupAsymptotics.CFSGGeckIntegralMatrices
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries

/-! The same normalized zero-or-one root-step entries hold integrally.
Rational casting recovers these integer equalities before any field
specialization; no root-string denominator is inverted in a field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepEntries
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
variable {n:Type*} [Fintype n] [DecidableEq n]
    (A:Matrix n n ℤ) (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b:(rootPairing A hs hp).Base)

private theorem cast_E_entry (i:b.support) (j k:b.support⊕Roots A) :
    ((CFSGGeckIntegralMatrices.E b i j k:ℤ):ℚ)=RootPairing.GeckConstruction.e i j k :=
  congrArg (fun M:Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>M j k)
    (CFSGGeckIntegralMatrices.map_E b i)

omit [Fintype (Roots A)] [DecidableEq (Roots A)] in
theorem root_add_iff_val (i j k:Roots A) :
    (rootPairing A hs hp).root k=(rootPairing A hs hp).root i+(rootPairing A hs hp).root j ↔
      k.val=i.val+j.val := by
  constructor
  · intro h
    funext t
    have ht:=congrFun h t
    change (k.val t:ℚ)=(i.val t:ℚ)+(j.val t:ℚ) at ht
    exact_mod_cast ht
  · intro h
    funext t
    change (k.val t:ℚ)=(i.val t:ℚ)+(j.val t:ℚ)
    rw [h]
    simp only [Pi.add_apply,Int.cast_add]

theorem E_inl_inl (i j k:b.support) :
    CFSGGeckIntegralMatrices.E b i (Sum.inl j) (Sum.inl k)=0 := rfl

theorem E_inl_inr (i j:b.support) (k:Roots A) :
    CFSGGeckIntegralMatrices.E b i (Sum.inl j) (Sum.inr k)=
      if j=i ∧ k.val= -(i:Roots A).val then 1 else 0 := by
  have h:=cast_E_entry A hs hp b i (Sum.inl j) (Sum.inr k)
  rw [CFSGNormTwoGeckNormalizedEntries.E_inl_inr A hs hp b] at h
  have hn:k=negativeIndex A hs hp i ↔ k.val= -(i:Roots A).val := by
    constructor
    · intro he
      subst k
      exact negative_val A hs hp i
    · intro he
      exact Subtype.ext (he.trans (negative_val A hs hp i).symm)
  simp only [hn] at h
  exact_mod_cast h

theorem E_inr_inl (i j:b.support) (k:Roots A) :
    CFSGGeckIntegralMatrices.E b i (Sum.inr k) (Sum.inl j)=
      if k.val=(i:Roots A).val then |b.cartanMatrix i j| else 0 := by
  have h:=cast_E_entry A hs hp b i (Sum.inr k) (Sum.inl j)
  rw [CFSGNormTwoGeckNormalizedEntries.E_inr_inl A hs hp b] at h
  have he:(k=(i:Roots A)) ↔ k.val=(i:Roots A).val:=Subtype.ext_iff
  simp only [he] at h
  exact_mod_cast h

theorem E_inr_inr (i:b.support) (j k:Roots A) :
    CFSGGeckIntegralMatrices.E b i (Sum.inr j) (Sum.inr k)=
      if j.val=(i:Roots A).val+k.val then 1 else 0 := by
  have h:=cast_E_entry A hs hp b i (Sum.inr j) (Sum.inr k)
  rw [CFSGNormTwoGeckNormalizedEntries.E_inr_inr A hs hp b] at h
  simp only [root_add_iff_val A hs hp] at h
  exact_mod_cast h

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepEntries
