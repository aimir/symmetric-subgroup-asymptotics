import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedCommonRatio

/-! The common mixed ratio is realized on EVERY zero-anisotropic
singular ray by a literal norm-lifted negative dilation of the original
nonsplit space. This supplies the full hyperbolic fixation needed by
the slice kernel, beyond fixation of the two coordinate halves. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDZeroAnisotropicDilation
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDMaximalSingularDimension
open CFSGTwistedDNegativeSpaceCoordinates CFSGTwistedDOpposedPieceExtension
open CFSGTwistedDHyperbolicCoordinates CFSGTwistedDLinearParameters
open CFSGTwistedDParameterSimilitudes CFSGTwistedDRelativeNormScaling
open CFSGTwistedDRelativeTorusParameters CFSGTwistedDOpposedCommonRatio CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticSubspacePoints

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem decompose_zero_anisotropic (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace n q) (hv : anisotropicPart n q v = 0) :
    v = positiveEmbedding n q (positivePart n q v) +
      negativeEmbedding n q (negativePart n q v) := by
  apply (linearParameters n q).injective
  rw [map_add, parameters_positive, parameters_negative]
  change (positivePart n q v, (negativePart n q v, anisotropicPart n q v)) = _
  simp only [hv, Prod.mk_add_mk, add_zero, zero_add]

theorem negativeDilation_zero_anisotropic (n : ℕ) (q : CFSG.PrimePower)
    (c : (q.Extension 2)ˣ) (v : fixedSpace n q) (hv : anisotropicPart n q v = 0) :
    negativeDilation n q c v = positiveEmbedding n q (positivePart n q v) +
      (normHom q c : fixedField q) • negativeEmbedding n q (negativePart n q v) := by
  apply (linearParameters n q).injective
  rw [negativeDilation_coordinates, map_add, map_smul, parameters_positive, parameters_negative]
  change (positivePart n q v,
    ((normHom q c : fixedField q) • negativePart n q v,
      (c : q.Extension 2) * anisotropicPart n q v)) = _
  simp only [hv, mul_zero, Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_add]

theorem exists_dilation (n : ℕ) (q : CFSG.PrimePower) (hn : 2 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q))))
    (hfixP : ∀ R : Points (fixedQuadraticForm n q), R.val ≤ positiveSpace n q → f R = R)
    (hfixZ : ∀ R : Points (fixedQuadraticForm n q), R.val ≤ negativeSpace n q → f R = R) :
    ∃ (t : fixedField q) (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q),
      t ≠ 0 ∧ (∀ v, fixedQuadraticForm n q (L v) = t * fixedQuadraticForm n q v) ∧
      ∀ (v : fixedSpace n q) (hv0 : v ≠ 0) (hQ : fixedQuadraticForm n q v = 0),
        anisotropicPart n q v = 0 →
        (f (ray (fixedQuadraticForm n q) v hv0 hQ)).val =
          Submodule.span (fixedField q) {L v} := by
  obtain ⟨t, ht, htr⟩ := exists_common_ratio n q hn f hlinear hfixP hfixZ
  obtain ⟨c, hc⟩ := normHom_surjective q (Units.mk0 t ht)
  have hct : (normHom q c : fixedField q) = t :=
    congrArg (fun z : (fixedField q)ˣ => (z : fixedField q)) hc
  refine ⟨t, negativeDilation n q c, ht, ?_, ?_⟩
  · intro v
    rw [negativeDilation_quadratic, hct]
  · intro v hv0 hQ ha
    let x := positiveEmbedding n q (positivePart n q v)
    let y := negativeEmbedding n q (negativePart n q v)
    have hx : x ∈ positiveSpace n q := ⟨positivePart n q v, rfl⟩
    have hy : y ∈ negativeSpace n q := ⟨negativePart n q v, rfl⟩
    have he : v = x + y := decompose_zero_anisotropic n q v ha
    have hD : negativeDilation n q c v = x + t • y := by
      rw [negativeDilation_zero_anisotropic n q c v ha, hct]
    let R := ray (fixedQuadraticForm n q) v hv0 hQ
    by_cases hx0 : x = 0
    · have hvy : v = y := by simpa only [hx0, zero_add] using he
      have hRy : R.val ≤ negativeSpace n q :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr (hvy ▸ hy)
      rw [hfixZ R hRy]
      change Submodule.span (fixedField q) {v} = Submodule.span (fixedField q) {_}
      rw [hD, hx0, zero_add, ← hvy]
      exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) v).symm
    by_cases hy0 : y = 0
    · have hvx : v = x := by simpa only [hy0, add_zero] using he
      have hRx : R.val ≤ positiveSpace n q :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr (hvx ▸ hx)
      rw [hfixP R hRx]
      change Submodule.span (fixedField q) {v} = Submodule.span (fixedField q) {_}
      rw [hD, hy0, smul_zero, add_zero, ← hvx]
    have hxy : (fixedQuadraticForm n q).polarBilin y x = 0 := by
      have heQ : fixedQuadraticForm n q (x + y) = 0 := he ▸ hQ
      rw [QuadraticMap.map_add (fixedQuadraticForm n q) x y] at heQ
      change fixedQuadraticForm n q x + fixedQuadraticForm n q y +
        (fixedQuadraticForm n q).polarBilin x y = 0 at heQ
      rw [(positiveSpace_maximal n q).1 x hx, negativeSpace_singular n q y hy,
        zero_add, zero_add] at heQ
      exact (QuadraticMap.polar_comm (fixedQuadraticForm n q) y x).trans heQ
    have hsum0 : x + y ≠ 0 := fun hz => hv0 (he.trans hz)
    have hsum : fixedQuadraticForm n q (x + y) = 0 := he ▸ hQ
    have hR : ray (fixedQuadraticForm n q) (x + y) hsum0 hsum = R := by
      apply Subtype.ext
      exact congrArg (fun z => Submodule.span (fixedField q) {z}) he.symm
    have h := htr x y hx hx0 hy hy0 hxy hsum0 hsum
    rw [hR] at h
    rw [hD]
    exact h

end SymmetricSubgroupAsymptotics.CFSGTwistedDZeroAnisotropicDilation
