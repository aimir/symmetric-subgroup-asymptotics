import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleSmallNumerics

/-!
# Nonsoluble primitive-affine sources at degrees 32, 49, 64 and 81

The integral composition-charge estimates for these four degrees are
packaged here as the concrete NSAPRIM sources consumed by the pre-`E₇`
catalogue.  The charts and chief traces are canonical; no finite census is
used.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineNonsolubleSmallSource

open PrimitiveAffineNonsolubleSmallNumerics

private noncomputable def source32
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 32)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 32 U) (Fin 32))
    (P : PrimitiveAffineProfile (preE7NonPairAction 32 U) (Fin 32))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 32 U := by
  let x : Fin 32 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (exponent_margin_32 hcomp U P hprimitive x C T hnonsolvable)

private noncomputable def source49
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 49)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 49 U) (Fin 49))
    (P : PrimitiveAffineProfile (preE7NonPairAction 49 U) (Fin 49))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 49 U := by
  let x : Fin 49 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (exponent_margin_49 hcomp U P hprimitive x C T hnonsolvable)

private noncomputable def source64
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 64)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 64 U) (Fin 64))
    (P : PrimitiveAffineProfile (preE7NonPairAction 64 U) (Fin 64))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 64 U := by
  let x : Fin 64 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (exponent_margin_64 hcomp U P hprimitive x C T hnonsolvable)

private noncomputable def source81
    (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass 81)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 81 U) (Fin 81))
    (P : PrimitiveAffineProfile (preE7NonPairAction 81 U) (Fin 81))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by norm_num⟩)) :
    PreE7RankTailOwnerSourceData 81 U := by
  let x : Fin 81 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact PrimitiveAffineNonsolubleSource.rankTailOwnerSourceDataOfMargin
    (by norm_num) (by norm_num) hprimitive P x C T hnonsolvable
    (exponent_margin_81 hcomp U P hprimitive x C T hnonsolvable)

/-- The four remaining nonsoluble affine profiles below degree `128` that
are closed by integral composition charge rather than by an action census. -/
noncomputable def primitiveAffineNonsolubleSmall_rankTailOwnerSourceData
    {w : ℕ} (hcomp : PrimitiveCompositionLengthInput)
    (U : PreE7NonPairActionClass w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hdegree : w = 32 ∨ w = 49 ∨ w = 64 ∨ w = 81) :
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by
        rcases hdegree with h32 | h49 | h64 | h81 <;> omega⟩)) →
    PreE7RankTailOwnerSourceData w U := by
  intro hnonsolvable
  by_cases h32 : w = 32
  · subst w
    exact source32 hcomp U hprimitive P hnonsolvable
  by_cases h49 : w = 49
  · subst w
    exact source49 hcomp U hprimitive P hnonsolvable
  by_cases h64 : w = 64
  · subst w
    exact source64 hcomp U hprimitive P hnonsolvable
  · have h81 : w = 81 := by
      rcases hdegree with h | h | h | h
      · exact False.elim (h32 h)
      · exact False.elim (h49 h)
      · exact False.elim (h64 h)
      · exact h
    subst w
    exact source81 hcomp U hprimitive P hnonsolvable

end PrimitiveAffineNonsolubleSmallSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
