import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarAutomorphismCoefficients
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace

/-! Actual scalar-centroid installation for the ORIGINAL automorphism
stabilizer of a singular two-plane. Every fixed scalar is transported
to one common fixed scalar on the entire Hermitian star, using actual
point-root covariance. This includes q=2 and ranks three and four;
fixed-field linearity is a conclusion to be reconstructed, not an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists

private theorem inverse_map_of_map_eq {A : Type*} [AddGroup A]
    (E : A ≃+ A) (L M : AddSubgroup A) (he : L.map E.toAddMonoidHom = M) :
    M.map E.symm.toAddMonoidHom = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← he] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    change E.symm (E z) ∈ L
    simpa only [AddEquiv.symm_apply_apply] using hz
  · intro hx
    refine ⟨E x, ?_, E.symm_apply_apply x⟩
    rw [← he]
    exact ⟨x, hx, rfl⟩

private theorem rankOneLine_zero {K : Type*} [Field K] (sigma : K ≃+* K)
    (hsigma : ∀ z, sigma (sigma z) = z) :
    CFSGHermitianTwoByTwoRankOne.rankOneLine sigma hsigma 0 = ⊥ := by
  apply le_antisymm
  · rintro A ⟨a, ha, rfl⟩
    apply AddSubgroup.mem_bot.mpr
    apply Subtype.ext
    ext i j
    change a * 0 * sigma 0 = 0
    rw [mul_zero, zero_mul]
  · exact bot_le

theorem unitaryStarCoefficientAut_permutes_rootLines (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    ∀ v : Fin 2 → q.Extension 2, ∃ w,
      (CFSGHermitianTwoByTwoRankOne.rankOneLine (definingFieldAutomorphism q 2)
        (fun z => extension_two_pow_twice q z) v).map
        (unitaryStarCoefficientAut q s t ht htc f hinc).symm.toAddMonoidHom =
      CFSGHermitianTwoByTwoRankOne.rankOneLine (definingFieldAutomorphism q 2)
        (fun z => extension_two_pow_twice q z) w := by
  intro v
  by_cases hv : v = 0
  · refine ⟨0, ?_⟩
    rw [hv, rankOneLine_zero, AddSubgroup.map_bot]
  let P := (unitarySingularPointActionHom q s f).symm (starPoint q s v hv)
  have hP : P.val ≤ starPlane q s := by
    apply (hinc P).mp
    have he : unitarySingularPointActionHom q s f P = starPoint q s v hv :=
      (unitarySingularPointActionHom q s f).apply_symm_apply _
    rw [he]
    exact starPoint_le_starPlane q s v hv
  obtain ⟨w, hw, hew⟩ := exists_starPoint_of_le q s P hP
  have he : unitarySingularPointActionHom q s f (starPoint q s w hw) = starPoint q s v hv := by
    rw [hew]
    exact (unitarySingularPointActionHom q s f).apply_symm_apply _
  exact ⟨w, inverse_map_of_map_eq (unitaryStarCoefficientAut q s t ht htc f hinc) _ _
    (unitaryStarCoefficientAut_rootLine q s t ht htc f hinc w v hw hv he)⟩

theorem unitaryStarCoefficientAut_transports_fixed_scalars (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s)
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a) :
    ∃ (b : q.Extension 2) (hb : definingFieldAutomorphism q 2 b = b),
      ∀ A : CFSGHermitianTwoByTwoRankOne.parameters (definingFieldAutomorphism q 2),
        unitaryStarCoefficientAut q s t ht htc f hinc
          (CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2) a ha A) =
        CFSGHermitianTwoByTwoRankOne.fixedScaleHom (definingFieldAutomorphism q 2) b hb
          (unitaryStarCoefficientAut q s t ht htc f hinc A) := by
  obtain ⟨theta, htheta⟩ := CFSGTwistedAQuadraticTrace.exists_trace_eq_fixed q 1 (map_one _)
  exact CFSGHermitianTwoByTwoRankOne.rootLinePermutation_transports_scalars
    (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z)
    (CFSGTwistedAQuadraticTrace.exists_nonfixed q) theta htheta
    (unitaryStarCoefficientAut q s t ht htc f hinc)
    (unitaryStarCoefficientAut_permutes_rootLines q s t ht htc f hinc) a ha

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
