import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarFixedField
import SymmetricSubgroupAsymptotics.CFSGTwistedAFixedFieldAutomorphismLift
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoAxes

/-! Actual extension-scalar installer and actual cone preservation.
The base-field automorphism is the one reconstructed from the ORIGINAL
star centroid, and the extension is a proved lift in the SAME quadratic
field. Cone preservation follows from original point-root covariance,
not from an orthogonal-geometry or linearity assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedA2FixedField

theorem unitaryStarCoefficientAut_preserves_cone (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s)
    (A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2))
    (hA : A.val.det = 0) :
    (unitaryStarCoefficientAut q s t ht htc f hinc A).val.det = 0 := by
  by_cases hz : A.val = 0
  · have hz' : A = 0 := Subtype.ext hz
    rw [hz', map_zero]
    change (0 : Matrix (Fin 2) (Fin 2) (q.Extension 2)).det = 0
    exact Matrix.det_zero (R := q.Extension 2) (n := Fin 2) inferInstance
  obtain ⟨a, v, ha, haf, hv, he⟩ :=
    (CFSGHermitianTwoByTwoRankOne.parameter_det_zero_iff_rankOne (definingFieldAutomorphism q 2) A hz).mp hA
  have hpoint : (unitarySingularPointActionHom q s f (starPoint q s v hv)).val ≤ starPlane q s :=
    (hinc (starPoint q s v hv)).mpr (starPoint_le_starPlane q s v hv)
  obtain ⟨w, hw, hew⟩ := exists_starPoint_of_le q s
    (unitarySingularPointActionHom q s f (starPoint q s v hv)) hpoint
  have hline := unitaryStarCoefficientAut_rootLine q s t ht htc f hinc v w hv hw hew.symm
  have hm : unitaryStarCoefficientAut q s t ht htc f hinc A ∈
      CFSGHermitianTwoByTwoRankOne.rankOneLine (definingFieldAutomorphism q 2)
        (fun z => extension_two_pow_twice q z) w := by
    rw [← hline]
    exact ⟨A, ⟨a, haf, Subtype.ext he⟩, rfl⟩
  obtain ⟨b, hb, hE⟩ := hm
  rw [hE]
  exact CFSGHermitianTwoByTwoRankOne.rankOne_det (definingFieldAutomorphism q 2) b w

theorem exists_unitaryStar_extension_semilinear (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      ∃ hcomm : Function.Commute (definingFieldAutomorphism q 2) tau,
      ∀ (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
        (A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2)),
        unitaryStarCoefficientAut q s t ht htc f hinc
          (CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2) a ha A) =
        CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2) (tau a)
          (CFSGHermitianTwoByTwoRankOne.automorphism_fixed_of_commute
            (definingFieldAutomorphism q 2) tau hcomm a ha)
          (unitaryStarCoefficientAut q s t ht htc f hinc A) := by
  obtain ⟨tau, htau, hcomm⟩ := exists_fixedField_automorphism_lift q (unitaryStarFixedFieldAut q s t ht htc f hinc)
  refine ⟨tau, hcomm, ?_⟩
  intro a ha A
  have he := unitaryStarFixedFieldAut_intertwines q s t ht htc f hinc ⟨a, ha⟩ A
  have hta : tau a = (unitaryStarFixedFieldAut q s t ht htc f hinc ⟨a, ha⟩).val := htau ⟨a, ha⟩
  change unitaryStarCoefficientAut q s t ht htc f hinc
    (CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2) a ha A) =
      CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2)
        (unitaryStarFixedFieldAut q s t ht htc f hinc ⟨a, ha⟩).val
        (unitaryStarFixedFieldAut q s t ht htc f hinc ⟨a, ha⟩).property
        (unitaryStarCoefficientAut q s t ht htc f hinc A) at he
  simpa only [← hta] using he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
