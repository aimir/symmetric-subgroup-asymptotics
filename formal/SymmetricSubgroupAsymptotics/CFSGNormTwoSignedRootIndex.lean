import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceFamily

/-! Literal signed positive-root indices embed in the actual full norm-two
root indices. Opposite roots and nonnegative roots cannot coincide; this
uses the actual norm-two equation rather than a root count or census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoSignedRootIndex
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoOriginalPositiveSources
open CFSGNormTwoOriginalSourceFamily
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)

def opposite (k : Roots A) : Roots A :=
  ⟨-k.val,by simp only [map_neg,LinearMap.neg_apply,neg_neg,k.property]⟩

theorem opposite_involutive (k : Roots A) : opposite A (opposite A k)=k := by
  apply Subtype.ext
  exact neg_neg k.val

theorem opposite_positive_ne_positive (k p : Positive A) : opposite A k.val≠p.val := by
  intro h
  have hz : k.val.val=0 := by
    funext a
    change k.val.val a=0
    have he:=congrFun (congrArg Subtype.val h) a
    change -k.val.val a=p.val.val a at he
    have hk:=k.property a
    have hp:=p.property a
    omega
  have hn:=k.val.property
  simp only [hz,map_zero,LinearMap.zero_apply] at hn
  norm_num at hn

def signedRoot (j : Bool×Positive A) : Roots A :=
  if j.1 then opposite A j.2.val else j.2.val

theorem signedRoot_injective : Function.Injective (signedRoot A) := by
  rintro ⟨b,k⟩ ⟨c,p⟩ h
  cases b <;> cases c
  · change k.val=p.val at h
    exact congrArg (fun q : Positive A=>(false,q)) (Subtype.ext h)
  · change k.val=opposite A p.val at h
    exact (opposite_positive_ne_positive A p k h.symm).elim
  · change opposite A k.val=p.val at h
    exact (opposite_positive_ne_positive A k p h).elim
  · change opposite A k.val=opposite A p.val at h
    have hi:=congrArg (opposite A) h
    rw [opposite_involutive,opposite_involutive] at hi
    exact congrArg (fun q : Positive A=>(true,q)) (Subtype.ext hi)

/-- SAME original family index, with all six/eight/etc Cartan directions
retained separately from the signed roots. -/
def familyIndex : BasisIndex A↪(Roots A⊕Fin r) where
  toFun j:=match j with | .inl a=>.inr a | .inr p=>.inl (signedRoot A p)
  inj' j k h:=by
    cases j with
    | inl a =>
      cases k with
      | inl b =>
        change Sum.inr a=Sum.inr b at h
        exact congrArg Sum.inl (Sum.inr.inj h)
      | inr q => cases h
    | inr p =>
      cases k with
      | inl a => cases h
      | inr q =>
        change Sum.inl (signedRoot A p)=Sum.inl (signedRoot A q) at h
        exact congrArg Sum.inr (signedRoot_injective A (Sum.inl.inj h))

end SymmetricSubgroupAsymptotics.CFSGNormTwoSignedRootIndex
