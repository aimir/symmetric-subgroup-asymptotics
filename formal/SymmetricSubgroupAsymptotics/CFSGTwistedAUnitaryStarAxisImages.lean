import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarExtensionSemilinearity
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoAxisNormalization
import SymmetricSubgroupAsymptotics.CFSGTwoCoordinateRays

/-! The two axis images used in the generic congruence normalization
come from the ACTUAL ORIGINAL point permutation. Their distinctness,
nonzero coefficients and nonzero wedge are proved here; none is an
additional original-model recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

private theorem basisVector0_ne_zero (q : CFSG.PrimePower) : (![1, 0] : Fin 2 → q.Extension 2) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)

private theorem basisVector1_ne_zero (q : CFSG.PrimePower) : (![0, 1] : Fin 2 → q.Extension 2) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 1)

theorem starPoint_eq_of_wedge_zero (q : CFSG.PrimePower) (s : ℕ)
    (v w : Fin 2 → q.Extension 2) (hv : v ≠ 0) (hw : w ≠ 0)
    (hdet : v 0 * w 1 - v 1 * w 0 = 0) : starPoint q s v hv = starPoint q s w hw := by
  obtain ⟨c, hc⟩ := CFSGTwoCoordinateRays.exists_smul_of_wedge_zero v w hw hdet
  have hc0 : c ≠ 0 := by
    intro hz
    apply hv
    simpa only [hz, zero_smul] using hc
  have hvec : starVector q s v = c • starVector q s w := by
    change starVectorLinear q s v = c • starVectorLinear q s w
    rw [hc, map_smul]
  apply Subtype.ext
  change (q.Extension 2) ∙ starVector q s v = (q.Extension 2) ∙ starVector q s w
  rw [hvec]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) _

theorem starPoint_basis_distinct (q : CFSG.PrimePower) (s : ℕ) :
    starPoint q s ![1, 0] (basisVector0_ne_zero q) ≠ starPoint q s ![0, 1] (basisVector1_ne_zero q) := by
  intro he
  have hspan : (q.Extension 2) ∙ starVector q s ![1, 0] = (q.Extension 2) ∙ starVector q s ![0, 1] :=
    congrArg (fun P : unitarySingularPoints q s => P.val) he
  have hm : starVector q s ![1, 0] ∈ (q.Extension 2) ∙ starVector q s ![0, 1] := by
    rw [← hspan]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have h0 := congrFun hc (starPositive s 0)
  change c * starVector q s ![0, 1] (starPositive s 0) = starVector q s ![1, 0] (starPositive s 0) at h0
  rw [starVector_positive, starVector_positive] at h0
  change c * 0 = 1 at h0
  rw [mul_zero] at h0
  exact zero_ne_one h0

theorem exists_unitaryStar_axis_images (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    ∃ (a b : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
      (hb : definingFieldAutomorphism q 2 b = b), a ≠ 0 ∧ b ≠ 0 ∧
      ∃ v w : Fin 2 → q.Extension 2, v 0 * w 1 - v 1 * w 0 ≠ 0 ∧
        unitaryStarCoefficientAut q s t ht htc f hinc
          (CFSGHermitianTwoByTwoRankOne.axis0 (definingFieldAutomorphism q 2) 1 (map_one _)) =
          CFSGHermitianTwoByTwoRankOne.rankOneParameter (definingFieldAutomorphism q 2)
            (fun z => extension_two_pow_twice q z) a ha v ∧
        unitaryStarCoefficientAut q s t ht htc f hinc
          (CFSGHermitianTwoByTwoRankOne.axis1 (definingFieldAutomorphism q 2) 1 (map_one _)) =
          CFSGHermitianTwoByTwoRankOne.rankOneParameter (definingFieldAutomorphism q 2)
            (fun z => extension_two_pow_twice q z) b hb w := by
  let sigma := definingFieldAutomorphism q 2
  let E := unitaryStarCoefficientAut q s t ht htc f hinc
  have hP0 := (hinc (starPoint q s ![1, 0] (basisVector0_ne_zero q))).mpr
    (starPoint_le_starPlane q s ![1, 0] (basisVector0_ne_zero q))
  have hP1 := (hinc (starPoint q s ![0, 1] (basisVector1_ne_zero q))).mpr
    (starPoint_le_starPlane q s ![0, 1] (basisVector1_ne_zero q))
  obtain ⟨v, hv, he0⟩ := exists_starPoint_of_le q s _ hP0
  obtain ⟨w, hw, he1⟩ := exists_starPoint_of_le q s _ hP1
  have hL0 := unitaryStarCoefficientAut_rootLine q s t ht htc f hinc ![1, 0] v (basisVector0_ne_zero q) hv he0.symm
  have hL1 := unitaryStarCoefficientAut_rootLine q s t ht htc f hinc ![0, 1] w (basisVector1_ne_zero q) hw he1.symm
  have hm0 : E (CFSGHermitianTwoByTwoRankOne.axis0 sigma 1 (map_one sigma)) ∈
      CFSGHermitianTwoByTwoRankOne.rankOneLine sigma (fun z => extension_two_pow_twice q z) v := by
    rw [← hL0]
    refine ⟨_, ⟨1, map_one sigma, ?_⟩, rfl⟩
    exact CFSGHermitianTwoByTwoRankOne.axis0_eq_rankOne sigma (fun z => extension_two_pow_twice q z) 1 (map_one sigma)
  have hm1 : E (CFSGHermitianTwoByTwoRankOne.axis1 sigma 1 (map_one sigma)) ∈
      CFSGHermitianTwoByTwoRankOne.rankOneLine sigma (fun z => extension_two_pow_twice q z) w := by
    rw [← hL1]
    refine ⟨_, ⟨1, map_one sigma, ?_⟩, rfl⟩
    exact CFSGHermitianTwoByTwoRankOne.axis1_eq_rankOne sigma (fun z => extension_two_pow_twice q z) 1 (map_one sigma)
  obtain ⟨a, ha, hea⟩ := hm0
  obtain ⟨b, hb, heb⟩ := hm1
  have ha0 : a ≠ 0 := by
    intro hz
    have hzE : E (CFSGHermitianTwoByTwoRankOne.axis0 sigma 1 (map_one sigma)) = 0 := by
      rw [hea]
      apply Subtype.ext
      ext i j
      change a * v i * sigma (v j) = 0
      simp only [hz, zero_mul]
    have hh := E.injective (hzE.trans (map_zero E).symm)
    exact one_ne_zero (congrArg (fun A : CFSGHermitianTwoByTwoRankOne.parameters sigma => A.val 0 0) hh)
  have hb0 : b ≠ 0 := by
    intro hz
    have hzE : E (CFSGHermitianTwoByTwoRankOne.axis1 sigma 1 (map_one sigma)) = 0 := by
      rw [heb]
      apply Subtype.ext
      ext i j
      change b * w i * sigma (w j) = 0
      simp only [hz, zero_mul]
    have hh := E.injective (hzE.trans (map_zero E).symm)
    exact one_ne_zero (congrArg (fun A : CFSGHermitianTwoByTwoRankOne.parameters sigma => A.val 1 1) hh)
  have hdet : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro hz
    have he := starPoint_eq_of_wedge_zero q s v w hv hw hz
    have hin := (unitarySingularPointActionHom q s f).injective (he0.symm.trans (he.trans he1))
    exact starPoint_basis_distinct q s hin
  exact ⟨a, b, ha, hb, ha0, hb0, v, w, hdet, hea, heb⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
