import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedTailOrthogonality

/-! An actual singular axis and three companions admit a singular
bridge perpendicular to the axis and nonorthogonal to all companions.
The exact not-both-R11 condition is retained; no three-hyperplane
avoidance inference is made over F2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDStarVectorBridge
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDPlaneRootLine CFSGTwistedDSingularDimensionBound
open CFSGTwistedDFixedTailLinear CFSGTwistedDDoubleTailEmbedding
open CFSGTwistedDHyperbolicTripleBridge CFSGTwistedDFixedTailOrthogonality CFSGTwistedA2FixedField

theorem exists_star_vector (s : ℕ) (q : CFSG.PrimePower)
    (u v w t : fixedSpace (s + 2) q) (hu : u ≠ 0)
    (hnt : ∀ a : fixedField q, t ≠ a • u)
    (hQu : fixedQuadraticForm (s + 2) q u = 0)
    (hQv : fixedQuadraticForm (s + 2) q v = 0)
    (hQw : fixedQuadraticForm (s + 2) q w = 0)
    (hQt : fixedQuadraticForm (s + 2) q t = 0)
    (huv : (fixedQuadraticForm (s + 2) q).polarBilin u v = 0)
    (huw : (fixedQuadraticForm (s + 2) q).polarBilin u w = 0)
    (hut : (fixedQuadraticForm (s + 2) q).polarBilin u t = 0)
    (hvw : (fixedQuadraticForm (s + 2) q).polarBilin v w ≠ 0)
    (havoid : (fixedQuadraticForm (s + 2) q).polarBilin v t = 0 ∨
      (fixedQuadraticForm (s + 2) q).polarBilin w t = 0) :
    ∃ d : fixedSpace (s + 2) q, fixedQuadraticForm (s + 2) q d = 0 ∧
      (fixedQuadraticForm (s + 2) q).polarBilin u d = 0 ∧
      (fixedQuadraticForm (s + 2) q).polarBilin v d ≠ 0 ∧
      (fixedQuadraticForm (s + 2) q).polarBilin w d ≠ 0 ∧
      (fixedQuadraticForm (s + 2) q).polarBilin t d ≠ 0 := by
  let A := fixedQuadraticForm (s + 2) q
  let B := A.polarBilin
  have hraw := congrArg (fun a : fixedField q => (a : q.Extension 2)) hQu
  dsimp only at hraw
  rw [fixedQuadraticForm_apply] at hraw
  obtain ⟨g, hg⟩ := CFSGTwistedDAllRankSingularOrbit.exists_normalize_all (s + 2) q
    u.val u.property hraw (fun he => hu (Subtype.ext he))
  let L := fixedLinearHom (s + 2) q g
  have hgu : L u = firstAxis (s + 2) q := by
    apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hg
  have hneg (x : fixedSpace (s + 2) q) (hx : B u x = 0) : negativeHead (s + 1) q (L x) = 0 := by
    rw [← positive_axis_polar, ← hgu]
    exact (fixedLinearHom_preserves_polar (s + 2) q g u x).trans hx
  have hv0 := hneg v huv
  have hw0 := hneg w huw
  have ht0 := hneg t hut
  let v1 := tailLinear (s + 1) q (L v)
  let w1 := tailLinear (s + 1) q (L w)
  let t1 := tailLinear (s + 1) q (L t)
  have hQtail (x : fixedSpace (s + 2) q) (hx : negativeHead (s + 1) q (L x) = 0)
      (hxQ : A x = 0) : fixedQuadraticForm (s + 1) q (tailLinear (s + 1) q (L x)) = 0 :=
    (tail_quadratic_of_negativeHead_zero (s + 1) q (L x) hx).trans
      ((fixedLinearHom_preserves_Q (s + 2) q g x).trans hxQ)
  have hBtail (x y : fixedSpace (s + 2) q)
      (hx : negativeHead (s + 1) q (L x) = 0) (hy : negativeHead (s + 1) q (L y) = 0) :
      (fixedQuadraticForm (s + 1) q).polarBilin
        (tailLinear (s + 1) q (L x)) (tailLinear (s + 1) q (L y)) = B x y :=
    (tail_polar_of_negativeHead_zero (s + 1) q (L x) (L y) hx hy).trans
      (fixedLinearHom_preserves_polar (s + 2) q g x y)
  have htind (a : fixedField q) : L t ≠ a • firstAxis (s + 2) q := by
    intro he
    apply hnt a
    apply L.injective
    rw [map_smul, hgu]
    exact he
  have ht1 : t1 ≠ 0 := tail_nonzero_of_not_axis (s + 1) q (L t) ht0 htind
  have hvw1 : (fixedQuadraticForm (s + 1) q).polarBilin v1 w1 ≠ 0 :=
    (hBtail v w hv0 hw0).trans_ne hvw
  have hav1 : (fixedQuadraticForm (s + 1) q).polarBilin v1 t1 = 0 ∨
      (fixedQuadraticForm (s + 1) q).polarBilin w1 t1 = 0 := by
    rcases havoid with hv | hw
    · exact Or.inl ((hBtail v t hv0 ht0).trans hv)
    · exact Or.inr ((hBtail w t hw0 ht0).trans hw)
  obtain ⟨d1, hd1, hvd1, hwd1, htd1⟩ := exists_triple_bridge s q v1 w1 t1
    (hQtail v hv0 hQv) (hQtail w hw0 hQw) (hQtail t ht0 hQt) ht1 hvw1 hav1
  let d0 := tailEmbed (s + 1) q d1
  let d := L.symm d0
  have hLd : L d = d0 := L.apply_symm_apply d0
  have hd0 : A d0 = 0 := (tailEmbed_quadratic (s + 1) q d1).trans hd1
  have hud0 : B (firstAxis (s + 2) q) d0 = 0 := by
    rw [positive_axis_polar]
    exact tailEmbed_negativeHead (s + 1) q d1
  have hnonzero (x : fixedSpace (s + 2) q) (hx : negativeHead (s + 1) q (L x) = 0)
      (hxB : (fixedQuadraticForm (s + 1) q).polarBilin
        (tailLinear (s + 1) q (L x)) d1 ≠ 0) : B x d ≠ 0 := by
    have he := fixedLinearHom_preserves_polar (s + 2) q g x d
    rw [hLd, tailEmbed_pairing (s + 1) q (L x) hx d1] at he
    exact he.symm.trans_ne hxB
  refine ⟨d, (fixedLinearHom_preserves_Q (s + 2) q g d).symm.trans
    (by rw [hLd]; exact hd0), ?_, hnonzero v hv0 hvd1, hnonzero w hw0 hwd1, hnonzero t ht0 htd1⟩
  have he := fixedLinearHom_preserves_polar (s + 2) q g u d
  rw [hgu, hLd] at he
  exact he.symm.trans hud0

end SymmetricSubgroupAsymptotics.CFSGTwistedDStarVectorBridge
