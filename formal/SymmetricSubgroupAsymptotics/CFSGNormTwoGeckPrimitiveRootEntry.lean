import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNormalizedEntries
import SymmetricSubgroupAsymptotics.CFSGGeckIntegralMatrices

/-! Both original integral Geck root operators have an actual unit
coefficient. These entries certify primitivity before any base change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPrimitiveRootEntry
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckNormalizedEntries
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem integer_E_unit_entry (i : b.support) :
    CFSGGeckIntegralMatrices.E b i (.inl i) (.inr (negativeIndex A hs hp i))=1 := by
  apply (Int.cast_injective (α:=ℚ))
  have hh := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>
    M (.inl i) (.inr (negativeIndex A hs hp i))) (CFSGGeckIntegralMatrices.map_E b i)
  dsimp only at hh
  change (CFSGGeckIntegralMatrices.E b i (.inl i) (.inr (negativeIndex A hs hp i)):ℚ)=_ at hh
  rw [hh,E_inl_inr]
  simp

theorem integer_F_unit_entry (i : b.support) :
    CFSGGeckIntegralMatrices.F b i (.inl i) (.inr (i:Roots A))=1 := by
  apply (Int.cast_injective (α:=ℚ))
  have hh := congrArg (fun M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ=>
    M (.inl i) (.inr (i:Roots A))) (CFSGGeckIntegralMatrices.map_F b i)
  dsimp only at hh
  change (CFSGGeckIntegralMatrices.F b i (.inl i) (.inr (i:Roots A)):ℚ)=_ at hh
  rw [hh]
  simp [RootPairing.GeckConstruction.f]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPrimitiveRootEntry
