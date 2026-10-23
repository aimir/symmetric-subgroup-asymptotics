import SymmetricSubgroupAsymptotics.CFSGTwistedDSliceTailPairing
import SymmetricSubgroupAsymptotics.CFSGFinitePairingPreserver

/-! After fixing every actual singular point of the hyperbolic part,
the remaining point action is induced by an actual linear norm isometry
on the anisotropic coordinate. The ambient map is formed on the SAME
fixed quadratic space, with no recognition or lifting premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDZeroHyperbolicKernel
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDSliceCoordinates
open CFSGTwistedDNormalizedSliceImages CFSGTwistedDSliceTailPairing
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem exists_linear_isometry (n : ℕ) (q : CFSG.PrimePower) (hn : 1 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hfix : ∀ P : Points (fixedQuadraticForm n q),
      (∀ v ∈ P.val, anisotropicPart n q v = 0) → f P = P)
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q)))) :
    ∃ L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q,
      (∀ v, fixedQuadraticForm n q (L v) = fixedQuadraticForm n q v) ∧
      ∀ P : Points (fixedQuadraticForm n q), (f P).val = P.val.map L.toLinearMap := by
  classical
  obtain ⟨psi, hzero, hnorm, hpair, hspec⟩ :=
    exists_pairing_preserving_tail n q hn f horth hfix hlinear
  let T : q.Extension 2 ≃ₗ[fixedField q] q.Extension 2 :=
    CFSGFinitePairingPreserver.linearEquiv (normForm q).polarBilin
      (polar_left_nondegenerate q) psi hpair
  have hT (a : q.Extension 2) : T a = psi a := rfl
  let L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q :=
    ((splitEquiv n q).trans
      ((LinearEquiv.refl (fixedField q)
        ((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))).prodCongr T)).trans
      (splitEquiv n q).symm
  have hL (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
      (a : q.Extension 2) : L (sliceVector n q h a) = sliceVector n q h (psi a) := by
    change (splitEquiv n q).symm
      (((LinearEquiv.refl (fixedField q)
        ((Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))).prodCongr T)
          (splitEquiv n q (sliceVector n q h a))) = _
    simp only [split_sliceVector, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, hT]
    rfl
  have hcoord (v : fixedSpace n q) :
      sliceVector n q (hyperbolicPart n q v) (anisotropicPart n q v) = v := by
    change (splitEquiv n q).symm (splitEquiv n q v) = v
    exact (splitEquiv n q).symm_apply_apply v
  have hgeneral (v : fixedSpace n q) :
      L v = sliceVector n q (hyperbolicPart n q v) (psi (anisotropicPart n q v)) := by
    conv_lhs => rw [← hcoord v]
    exact hL _ _
  refine ⟨L, ?_, ?_⟩
  · intro v
    rw [hgeneral, quadratic_sliceVector, hnorm]
    change dotProduct (positivePart n q v) (negativePart n q v) +
      normForm q (anisotropicPart n q v) = fixedQuadraticForm n q v
    exact (quadratic_parts n q v).symm
  · intro P
    obtain ⟨v, hv, hv0⟩ := point_nonzero (fixedQuadraticForm n q) P
    have hP := point_span (fixedQuadraticForm n q) P v hv hv0
    have hmap : P.val.map L.toLinearMap = Submodule.span (fixedField q) {L v} := by
      rw [← hP, Submodule.map_span, Set.image_singleton]
      rfl
    by_cases ha : anisotropicPart n q v = 0
    · have hfixP : f P = P := hfix P (by
        intro x hx
        rw [← hP] at hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, ha, smul_zero])
      have hLv : L v = v := by
        rw [hgeneral, ha, hzero]
        simpa only [ha] using hcoord v
      rw [hfixP, hmap, hLv]
      exact hP.symm
    · let h := hyperbolicPart n q v
      let a := anisotropicPart n q v
      have hh : dotProduct h.1 h.2 = -normForm q a := by
        have hvQ := P.property.2 v hv
        rw [quadratic_parts] at hvQ
        exact eq_neg_of_add_eq_zero_left hvQ
      have heP : slicePoint n q a ha h hh = P := by
        apply Subtype.ext
        change Submodule.span (fixedField q) {sliceVector n q h a} = P.val
        rw [hcoord v]
        exact hP
      have he := hspec a ha h hh
      change (f (slicePoint n q a ha h hh)).val =
        Submodule.span (fixedField q) {sliceVector n q h (psi a)} at he
      rw [heP] at he
      rw [hmap, hgeneral]
      exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedDZeroHyperbolicKernel
