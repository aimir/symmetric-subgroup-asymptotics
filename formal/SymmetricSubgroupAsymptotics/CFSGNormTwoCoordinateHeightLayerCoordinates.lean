import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightFactorUniqueness

/-! Independent additive coordinates for the ACTUAL height-h image in
U/U_(h+1). Injectivity is proved by the checked height-factor uniqueness;
the product chart and its full range are not new hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerCoordinates
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateHeightLayerFactorization
open CFSGNormTwoCoordinateHeightFactorUniqueness CFSGNormTwoCoordinateExactHeightWordLeading
open CFSGFiniteQuotientFamilyProduct
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem productHom_eq_word (K : Type) [Field K] (h : ℤ) (hh : 0 < h)
    (c : ExactHeightRoot A h → Multiplicative K) :
    exactHeightProductHom A hd hs hp ho K h hh c =
      (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h + 1)))
        (exactHeightWord A hd hs hp ho K h (fun k => (c k).toAdd)) := by
  classical
  let q := QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h + 1))
  let f := fun k : ExactHeightRoot A h =>
    positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property
  have hc : Pairwise (fun i j : ExactHeightRoot A h =>
      ∀ a b, Commute (q (f i a)) (q (f j b))) := by
    intro i j hij a b
    exact quotient_root_images_commute A hd hs hp ho K h hh i.val.val j.val.val
      i.val.property j.val.property (le_of_eq i.property.symm)
      (le_of_eq j.property.symm) a b
  exact (orderedFamilyProduct_image q f hc c).symm

theorem productHom_injective (K : Type) [Field K] (h : ℤ) (hh : 0 < h) :
    Function.Injective (exactHeightProductHom A hd hs hp ho K h hh) := by
  classical
  apply (exactHeightProductHom A hd hs hp ho K h hh).ker_eq_bot_iff.mp
  apply bot_unique
  intro c hc
  have hw : (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h + 1)))
      (exactHeightWord A hd hs hp ho K h (fun k => (c k).toAdd)) = 1 := by
    rw [← productHom_eq_word A hd hs hp ho K h hh]
    exact hc
  have hm : exactHeightWord A hd hs hp ho K h (fun k => (c k).toAdd) ∈
      heightTailInPositive A hd hs hp ho K (h + 1) :=
    (QuotientGroup.eq_one_iff _).mp hw
  have he : exactHeightWord A hd hs hp ho K h (fun k => (c k).toAdd) * 1 =
      exactHeightWord A hd hs hp ho K h (fun _ => 0) *
        exactHeightWord A hd hs hp ho K h (fun k => (c k).toAdd) := by
    rw [exactHeightWord_zero, mul_one, one_mul]
  have hz := height_factor_parameters_unique A hd hs hp ho K h hh
    (fun k => (c k).toAdd) (fun _ => 0) 1
    (exactHeightWord A hd hs hp ho K h (fun k => (c k).toAdd))
    (one_mem _) hm he
  change c = 1
  funext k
  apply (Multiplicative.toAdd : Multiplicative K ≃ K).injective
  exact congrFun hz k

def heightLayerEquiv (K : Type) [Field K] (h : ℤ) (hh : 0 < h) :
    (ExactHeightRoot A h → Multiplicative K) ≃*
      (heightTailInPositive A hd hs hp ho K h).map
        (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h + 1))) :=
  (MonoidHom.ofInjective (productHom_injective A hd hs hp ho K h hh)).trans
    (MulEquiv.subgroupCongr (exactHeightProductHom_range A hd hs hp ho K h hh))

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerCoordinates
