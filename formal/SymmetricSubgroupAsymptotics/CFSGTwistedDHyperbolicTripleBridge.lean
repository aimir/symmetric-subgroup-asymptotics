import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedHyperbolicBridge
import SymmetricSubgroupAsymptotics.CFSGTwistedDRootPlaneImage
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDQuadraticPairTail

/-! Any actual hyperbolic pair and a third nonzero singular vector
orthogonal to at least one member admit a singular vector nonorthogonal
to all three. Literal relative words normalize the hyperbolic pair;
the final norm plane supplies the shell, including over F2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicTripleBridge
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexPrefixPerpendicular
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDPlaneRootLine CFSGTwistedDRootPlaneImage CFSGTwistedDSingularDimensionBound
open CFSGTwistedDFixedTailLinear CFSGTwistedA2FixedField

private theorem zero_ne_last (n : ℕ) : (0 : Fin (n + 3)) ≠ last (n + 1) := by
  intro h
  have he := congrArg Fin.val h
  change 0 = n + 2 at he
  omega

def negativeAxis (n : ℕ) (q : CFSG.PrimePower) : fixedSpace (n + 1) q :=
  negativeBasis (n + 1) q 0 (zero_ne_last n)

theorem positive_axis_polar (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace (n + 1) q) :
    (fixedQuadraticForm (n + 1) q).polarBilin (firstAxis (n + 1) q) z = negativeHead n q z := by
  apply Subtype.ext
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar]
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inl 0) 1) z.val = z.val (Sum.inr 0)
  rw [polar_positive_basis]

theorem negative_axis_polar (n : ℕ) (q : CFSG.PrimePower) (z : fixedSpace (n + 1) q) :
    (fixedQuadraticForm (n + 1) q).polarBilin (negativeAxis n q) z = positiveHead n q z := by
  apply Subtype.ext
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar]
  change CFSGOrthogonalDIndexPolarForm.polar (q.Extension 2)
    (Pi.single (Sum.inr 0) 1) z.val = z.val (Sum.inl 0)
  exact CFSGOrthogonalDQuadraticPairTail.pairing_first_negative (q.Extension 2) (n + 2) z.val

theorem exists_fixed_hyperbolic_frame (n : ℕ) (q : CFSG.PrimePower)
    (v w : fixedSpace (n + 1) q) (hv : v ≠ 0)
    (hvQ : fixedQuadraticForm (n + 1) q v = 0)
    (hwQ : fixedQuadraticForm (n + 1) q w = 0)
    (hB : (fixedQuadraticForm (n + 1) q).polarBilin v w = 1) :
    ∃ g : CFSGTwistedDRelativeElementaryGroup.relativeRootGroup (n + 1) q,
      fixedLinearHom (n + 1) q g v = firstAxis (n + 1) q ∧
      fixedLinearHom (n + 1) q g w = negativeAxis n q := by
  have hvK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hvQ
  have hwK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hwQ
  have hBK := congrArg (fun a : fixedField q => (a : q.Extension 2)) hB
  dsimp only at hvK hwK hBK
  rw [fixedQuadraticForm_apply] at hvK hwK
  rw [fixedQuadraticForm_polar, splitQuadraticForm_polar] at hBK
  obtain ⟨g, hgv, hgw⟩ := CFSGTwistedDAllRankHyperbolicPairs.exists_normalize_pair
    (n + 1) q v.val w.val v.property w.property hvK hwK
    (fun he => hv (Subtype.ext he)) hBK
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hgv
  · apply Subtype.ext
    rw [fixedLinearHom_apply]
    exact hgw

theorem exists_triple_bridge (n : ℕ) (q : CFSG.PrimePower)
    (v w t : fixedSpace (n + 1) q)
    (hvQ : fixedQuadraticForm (n + 1) q v = 0)
    (hwQ : fixedQuadraticForm (n + 1) q w = 0)
    (htQ : fixedQuadraticForm (n + 1) q t = 0) (ht : t ≠ 0)
    (hvw : (fixedQuadraticForm (n + 1) q).polarBilin v w ≠ 0)
    (havoid : (fixedQuadraticForm (n + 1) q).polarBilin v t = 0 ∨
      (fixedQuadraticForm (n + 1) q).polarBilin w t = 0) :
    ∃ d : fixedSpace (n + 1) q, fixedQuadraticForm (n + 1) q d = 0 ∧
      (fixedQuadraticForm (n + 1) q).polarBilin v d ≠ 0 ∧
      (fixedQuadraticForm (n + 1) q).polarBilin w d ≠ 0 ∧
      (fixedQuadraticForm (n + 1) q).polarBilin t d ≠ 0 := by
  let A := fixedQuadraticForm (n + 1) q
  let B := A.polarBilin
  let c := B v w
  have hc : c ≠ 0 := hvw
  let w1 := c⁻¹ • w
  have hv : v ≠ 0 := by
    intro he
    apply hvw
    simp only [he, map_zero, LinearMap.zero_apply]
  have hw1Q : A w1 = 0 := by
    rw [show w1 = c⁻¹ • w from rfl, A.map_smul, hwQ, smul_zero]
  have hB1 : B v w1 = 1 := by
    change B v (c⁻¹ • w) = 1
    rw [map_smul]
    change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc
  obtain ⟨g, hgv, hgw⟩ := exists_fixed_hyperbolic_frame n q v w1 hv hvQ hw1Q hB1
  let L := fixedLinearHom (n + 1) q g
  let t0 := L t
  have ht0 : t0 ≠ 0 := by
    intro he
    exact ht (L.injective (he.trans L.map_zero.symm))
  have ht0Q : A t0 = 0 := (fixedLinearHom_preserves_Q (n + 1) q g t).trans htQ
  have hav : positiveHead n q t0 = 0 ∨ negativeHead n q t0 = 0 := by
    rcases havoid with hvt | hwt
    · right
      rw [← positive_axis_polar, ← hgv]
      exact (fixedLinearHom_preserves_polar (n + 1) q g v t).trans hvt
    · left
      rw [← negative_axis_polar, ← hgw]
      have hwtB : B w t = 0 := hwt
      exact (fixedLinearHom_preserves_polar (n + 1) q g w1 t).trans
        (by change B (c⁻¹ • w) t = 0; simp only [map_smul, LinearMap.smul_apply, hwtB, smul_zero])
  obtain ⟨d0, hd0, hdp, hdn, htd⟩ :=
    CFSGTwistedDNormalizedHyperbolicBridge.exists_bridge n q t0 ht0 ht0Q hav
  let d := L.symm d0
  have hLd : L d = d0 := L.apply_symm_apply d0
  have hvd : B v d = 1 := by
    have he := fixedLinearHom_preserves_polar (n + 1) q g v d
    rw [hgv, hLd, positive_axis_polar, hdn] at he
    exact he.symm
  have hwd : B w d ≠ 0 := by
    have he := fixedLinearHom_preserves_polar (n + 1) q g w1 d
    rw [hgw, hLd, negative_axis_polar, hdp] at he
    intro hz
    change (1 : fixedField q) = B (c⁻¹ • w) d at he
    simp only [map_smul, LinearMap.smul_apply, hz, smul_zero] at he
    exact one_ne_zero he
  refine ⟨d, (fixedLinearHom_preserves_Q (n + 1) q g d).symm.trans
    (by rw [hLd]; exact hd0), hvd.trans_ne one_ne_zero, hwd, ?_⟩
  have he := fixedLinearHom_preserves_polar (n + 1) q g t d
  rw [hLd] at he
  exact he.symm.trans_ne htd

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicTripleBridge
