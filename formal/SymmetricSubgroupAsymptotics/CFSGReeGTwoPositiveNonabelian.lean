import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentralQuotient

/-! Concrete noncommuting elements of the actual positive group. They
remain noncommuting in the pinned Ree group under its faithful positive
embedding. No simplicity or exceptional order formula is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveNonabelian
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoFixedCoordinateArithmetic CFSGReeGTwoPositiveCentralQuotient
open CFSGGTwoPositiveSixWord CFSGGTwoPositiveWordMultiplication

theorem fixedPositive_noncommuting (m : ℕ) :
    ∃ u v : fixedPositiveGroup m, u*v≠v*u := by
  let u : fixedPositiveGroup m := fixedPositiveChart m ![0,1,0]
  let v : fixedPositiveGroup m := fixedPositiveChart m ![1,0,0]
  refine ⟨u,v,?_⟩
  intro he
  have hw :
      modelWord (Field m) (normalForm (alphaEquiv m) 0 1 0)*
        modelWord (Field m) (normalForm (alphaEquiv m) 1 0 0)=
      modelWord (Field m) (normalForm (alphaEquiv m) 1 0 0)*
        modelWord (Field m) (normalForm (alphaEquiv m) 0 1 0) :=
    congrArg (fun z : fixedPositiveGroup m => z.val.val) he
  rw [modelWord_mul,modelWord_mul] at hw
  have hc := congrFun (modelWord_injective (Field m) hw) 3
  have hn : (-1 : Field m)=0 := by
    simpa [productCoordinates,normalForm] using hc
  exact (neg_ne_zero.mpr (one_ne_zero : (1 : Field m)≠0)) hn

theorem reePositive_noncommuting (m : ℕ) (hm : 1≤m) :
    ∃ u v : (reePositiveHom m hm).range, u*v≠v*u := by
  obtain ⟨u,v,huv⟩ := fixedPositive_noncommuting m
  let f := (reePositiveHom m hm).rangeRestrict
  refine ⟨f u,f v,?_⟩
  intro he
  apply huv
  apply reePositiveHom_injective m hm
  simpa only [map_mul] using congrArg (fun z : (reePositiveHom m hm).range => z.val) he

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveNonabelian
