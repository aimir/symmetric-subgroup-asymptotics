import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicCoordinates
import SymmetricSubgroupAsymptotics.CFSGDotProductMixedProbes
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarPointFunctionals

/-! Fixing every actual singular point in the hyperbolic coordinate
sum forces ONE common nonzero scalar on both paired projections of
any image representative with nonzero paired dot product. The two
scalars are coupled on a genuine actual mixed singular plane; the
proof works unchanged in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicProjectionCoupling
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDMaximalSingularDimension CFSGTwistedDNegativeSpaceCoordinates
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexQuadraticSubspacePoints
open CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem paired_projections_common_scalar (n : ℕ) (q : CFSG.PrimePower) (hn : 1 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hfix : ∀ P : Points (fixedQuadraticForm n q),
      (∀ v ∈ P.val, anisotropicPart n q v = 0) → f P = P)
    (P : Points (fixedQuadraticForm n q)) (v w : fixedSpace n q)
    (hv : v ∈ P.val) (hw : w ∈ (f P).val) (hv0 : v ≠ 0) (hw0 : w ≠ 0)
    (hxy : dotProduct (positivePart n q v) (negativePart n q v) ≠ 0) :
    ∃ c : fixedField q, c ≠ 0 ∧
      positivePart n q w = c • positivePart n q v ∧
      negativePart n q w = c • negativePart n q v := by
  let A := fixedQuadraticForm n q
  let U : Subspaces A := ⟨positiveSpace n q, positiveSpace_singular n q⟩
  let Z : Subspaces A := ⟨negativeSpace n q, negativeSpace_singular n q⟩
  have hfixU (R : Points A) (hR : R.val ≤ U.val) : f R = R :=
    hfix R (fun z hz => anisotropicPart_zero_positiveSpace n q z (hR hz))
  have hfixZ (R : Points A) (hR : R.val ≤ Z.val) : f R = R :=
    hfix R (fun z hz => anisotropicPart_zero_negativeSpace n q z (hR hz))
  obtain ⟨p, r, hpr, hvp, hvr⟩ := CFSGDotProductMixedProbes.exists_mixed_probes
    (by simp only [Fintype.card_fin]; omega : 2 ≤ Fintype.card (Fin (n + 1)))
    (positivePart n q v) (negativePart n q v) hxy
  let a := positiveEmbedding n q p
  let b := negativeEmbedding n q r
  have ha : a ∈ U.val := ⟨p, rfl⟩
  have hb : b ∈ Z.val := ⟨r, rfl⟩
  have ha0 : anisotropicPart n q a = 0 := anisotropicPart_positive n q p
  have hb0 : anisotropicPart n q b = 0 := anisotropicPart_negative n q r
  have hVa : A.polarBilin v a ≠ 0 := by
    change (fixedQuadraticForm n q).polarBilin v (positiveEmbedding n q p) ≠ 0
    rw [polar_positive, dotProduct_comm]
    exact hvp
  have hVb : A.polarBilin v b ≠ 0 := by
    change (fixedQuadraticForm n q).polarBilin v (negativeEmbedding n q r) ≠ 0
    rw [polar_negative]
    exact hvr
  have hab : A.polarBilin a b = 0 := by
    change (fixedQuadraticForm n q).polarBilin (positiveEmbedding n q p) (negativeEmbedding n q r) = 0
    rw [polar_negative, positivePart_positive]
    exact hpr
  have hUn : restrictedPairing A U v ≠ 0 := by
    intro he
    exact hVa (LinearMap.congr_fun he ⟨a, ha⟩)
  have hZn : restrictedPairing A Z v ≠ 0 := by
    intro he
    exact hVb (LinearMap.congr_fun he ⟨b, hb⟩)
  obtain ⟨alpha, halpha, heA⟩ := restrictedPairing_proportional A f horth U hfixU
    P v w hv hw hv0 hw0 hUn
  obtain ⟨beta, hbeta, heB⟩ := restrictedPairing_proportional A f horth Z hfixZ
    P v w hv hw hv0 hw0 hZn
  have hTs : ∀ z ∈ Submodule.span (fixedField q) {a, b}, A z = 0 := by
    intro z hz
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [QuadraticMap.map_add A (c • a) (d • b)]
    change A (c • a) + A (d • b) + A.polarBilin (c • a) (d • b) = 0
    simp only [A.map_smul, U.property a ha, Z.property b hb, smul_zero,
      map_smul, LinearMap.smul_apply, hab, smul_eq_mul, mul_zero, add_zero]
  let T : Subspaces A := ⟨Submodule.span (fixedField q) {a, b}, hTs⟩
  have hTa : a ∈ T.val := Submodule.subset_span (by simp)
  have hTb : b ∈ T.val := Submodule.subset_span (by simp)
  have hTzero (z : fixedSpace n q) (hz : z ∈ T.val) : anisotropicPart n q z = 0 := by
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_smul, map_smul, ha0, hb0, smul_zero, smul_zero, add_zero]
  have hfixT (R : Points A) (hR : R.val ≤ T.val) : f R = R :=
    hfix R (fun z hz => hTzero z (hR hz))
  have hTn : restrictedPairing A T v ≠ 0 := by
    intro he
    exact hVa (LinearMap.congr_fun he ⟨a, hTa⟩)
  obtain ⟨gamma, hgamma, heT⟩ := restrictedPairing_proportional A f horth T hfixT
    P v w hv hw hv0 hw0 hTn
  have hAg : alpha = gamma := by
    have hA := LinearMap.congr_fun heA ⟨a, ha⟩
    have hT := LinearMap.congr_fun heT ⟨a, hTa⟩
    change A.polarBilin w a = alpha * A.polarBilin v a at hA
    change A.polarBilin w a = gamma * A.polarBilin v a at hT
    exact mul_right_cancel₀ hVa (hA.symm.trans hT)
  have hBg : beta = gamma := by
    have hB := LinearMap.congr_fun heB ⟨b, hb⟩
    have hT := LinearMap.congr_fun heT ⟨b, hTb⟩
    change A.polarBilin w b = beta * A.polarBilin v b at hB
    change A.polarBilin w b = gamma * A.polarBilin v b at hT
    exact mul_right_cancel₀ hVb (hB.symm.trans hT)
  have hBA : beta = alpha := hBg.trans hAg.symm
  refine ⟨alpha, halpha, ?_, ?_⟩
  · funext i
    have he := LinearMap.congr_fun heB
      ⟨negativeEmbedding n q (Pi.single i 1), ⟨Pi.single i 1, rfl⟩⟩
    change A.polarBilin w (negativeEmbedding n q (Pi.single i 1)) =
      beta * A.polarBilin v (negativeEmbedding n q (Pi.single i 1)) at he
    dsimp only [A] at he
    rw [polar_negative, polar_negative, dotProduct_single, dotProduct_single,
      mul_one, mul_one, hBA] at he
    exact he
  · funext i
    have he := LinearMap.congr_fun heA
      ⟨positiveEmbedding n q (Pi.single i 1), ⟨Pi.single i 1, rfl⟩⟩
    change A.polarBilin w (positiveEmbedding n q (Pi.single i 1)) =
      alpha * A.polarBilin v (positiveEmbedding n q (Pi.single i 1)) at he
    dsimp only [A] at he
    rw [polar_positive, polar_positive, single_dotProduct, single_dotProduct,
      one_mul, one_mul] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicProjectionCoupling
