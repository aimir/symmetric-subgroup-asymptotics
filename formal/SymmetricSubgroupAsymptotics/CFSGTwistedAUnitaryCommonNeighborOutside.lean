import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeadCorrectionOutside
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryIsotropicPointCoverage
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitarySubspaceAction

/-! Arbitrary-point transport of the literal outside common-neighbor
construction by the SAME original natural root word and its inverse.
No ambient isometry-extension or building-connectivity premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGTwistedAUnitaryParameters
open CFSGHermitianOrthogonalSpan

private theorem perp_image_member {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K) (e : (I → K) ≃ₗ[K] (I → K))
    (he : ∀ x y, hermitianPair sigma H (e x) (e y) = hermitianPair sigma H x y)
    (S : Submodule K (I → K)) (x : I → K) (hx : x ∈ rightPerp sigma H S) :
    e x ∈ rightPerp sigma H (S.map e.toLinearMap) := by
  rintro y ⟨z, hz, rfl⟩
  exact (he z x).trans (hx z hz)

private theorem span_pair_image {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) (x y z : V) (a : K) (ha : a ≠ 0) (hx : e x = a • z) :
    ((K ∙ x) ⊔ K ∙ y).map e.toLinearMap = (K ∙ z) ⊔ K ∙ e y := by
  rw [Submodule.map_sup, Submodule.map_span, Submodule.map_span,
    Set.image_singleton, Set.image_singleton]
  change (K ∙ e x) ⊔ (K ∙ e y) = (K ∙ z) ⊔ (K ∙ e y)
  rw [hx, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha)]

theorem exists_unitary_common_neighbor_outside (q : CFSG.PrimePower)
    (R S : Fin 5 → q.Extension 2) (hR0 : R ≠ 0) (hR : unitaryNaturalPair q 4 R R = 0)
    (hSR : unitaryNaturalPair q 4 S R ≠ 0)
    (W : Submodule (q.Extension 2) (Fin 5 → q.Extension 2))
    (hnot : ¬ rightPerp (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) W ≤
        ((q.Extension 2) ∙ R) ⊔ (q.Extension 2) ∙ S) :
    ∃ v : Fin 5 → q.Extension 2, v ≠ 0 ∧ unitaryNaturalPair q 4 v v = 0 ∧ v ∉ W ∧
      unitaryNaturalPair q 4 R v = 0 ∧ unitaryNaturalPair q 4 S v = 0 := by
  obtain ⟨g, a, ha, haxis⟩ := exists_isotropic_vector_axis q 2 R hR0 hR
  let e := unitaryNaturalLinearEquiv q 4 g
  let sig := definingFieldAutomorphism q 2
  let H : Mat (q.Extension 2) 4 := signedReversalUnit (q.Extension 2) 4
  let e₀ : Fin 5 → q.Extension 2 := Pi.single 0 1
  have heR : e R = a • e₀ := haxis
  have hform (x y : Fin 5 → q.Extension 2) :
      hermitianPair sig H (e x) (e y) = hermitianPair sig H x y :=
    unitaryNaturalLinearEquiv_pair q 4 g x y
  have hw : hermitianPair sig H (e S) e₀ ≠ 0 := by
    intro hz
    have hh := hform S R
    rw [heR] at hh
    have hs := hermitianPair_smul sig H 1 a (e S) e₀
    simp only [one_smul, map_one, one_mul, hz, mul_zero] at hs
    exact hSR (hh.symm.trans hs)
  have hnot' : ¬rightPerp sig H (W.map e.toLinearMap) ≤
      ((q.Extension 2) ∙ e₀) ⊔ (q.Extension 2) ∙ e S := by
    intro hbad
    apply hnot
    intro x hx
    have hm := hbad (perp_image_member sig H e hform W x hx)
    have hspan := span_pair_image e R S e₀ a ha heR
    rw [← hspan] at hm
    obtain ⟨y, hy, he⟩ := hm
    exact e.injective he ▸ hy
  obtain ⟨v, hv0, hvnorm, hvW, he₀v, hSv⟩ :=
    exists_unitary_head_common_neighbor_outside q (e S) hw (W.map e.toLinearMap) hnot'
  have hu0 : e.symm v ≠ 0 := by
    intro h
    have hh := congrArg e h
    rw [LinearEquiv.apply_symm_apply, map_zero] at hh
    exact hv0 hh
  refine ⟨e.symm v, hu0, ?_, ?_, ?_, ?_⟩
  · have hh : hermitianPair sig H v v = hermitianPair sig H (e.symm v) (e.symm v) := by
      simpa only [LinearEquiv.apply_symm_apply] using hform (e.symm v) (e.symm v)
    have hn : hermitianPair sig H v v = 0 := hvnorm
    exact hh.symm.trans hn
  · intro h
    exact hvW ⟨e.symm v, h, e.apply_symm_apply v⟩
  · have hh := hform R (e.symm v)
    rw [heR, LinearEquiv.apply_symm_apply] at hh
    have hs := hermitianPair_smul sig H a 1 e₀ v
    have hz : hermitianPair sig H e₀ v = 0 := he₀v
    simp only [one_smul, mul_one, hz, mul_zero] at hs
    exact hh.symm.trans hs
  · have hh := hform S (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh.symm.trans hSv

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
