import SymmetricSubgroupAsymptotics.CFSGTwistedDSliceTailConstancy
import SymmetricSubgroupAsymptotics.CFSGHyperbolicPrescribedGramPair

/-! A common actual image tail on each nonzero norm slice preserves the
anisotropic polar pairing. Two explicit hyperbolic coordinates prescribe
the required source orthogonality; no additivity of the tail is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDSliceTailPairing
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDSliceCoordinates
open CFSGTwistedDNormalizedSliceImages CFSGTwistedDSliceTailConstancy
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem exists_pairing_preserving_tail (n : ℕ) (q : CFSG.PrimePower) (hn : 1 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hfix : ∀ P : Points (fixedQuadraticForm n q),
      (∀ v ∈ P.val, anisotropicPart n q v = 0) → f P = P)
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q)))) :
    ∃ psi : q.Extension 2 → q.Extension 2,
      psi 0 = 0 ∧ (∀ a, normForm q (psi a) = normForm q a) ∧
      (∀ a b, (normForm q).polarBilin (psi a) (psi b) = (normForm q).polarBilin a b) ∧
      ∀ (a : q.Extension 2) (ha : a ≠ 0)
        (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
        (hh : dotProduct h.1 h.2 = -normForm q a),
          NormalizedImage n q f a ha h hh (psi a) := by
  classical
  let psi : q.Extension 2 → q.Extension 2 := fun a =>
    if ha : a = 0 then 0 else
      Classical.choose (exists_common_slice_tail n q hn f horth hfix hlinear a ha)
  have hzero : psi 0 = 0 := by simp only [psi, dif_pos rfl]
  have hspec (a : q.Extension 2) (ha : a ≠ 0) :
      normForm q (psi a) = normForm q a ∧
        ∀ (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
          (hh : dotProduct h.1 h.2 = -normForm q a),
            NormalizedImage n q f a ha h hh (psi a) := by
    dsimp only [psi]
    rw [dif_neg ha]
    exact Classical.choose_spec (exists_common_slice_tail n q hn f horth hfix hlinear a ha)
  refine ⟨psi, hzero, ?_, ?_, fun a ha => (hspec a ha).2⟩
  · intro a
    by_cases ha : a = 0
    · rw [ha, hzero]
    · exact (hspec a ha).1
  · intro a b
    by_cases ha : a = 0
    · simp only [ha, hzero, map_zero, LinearMap.zero_apply]
    by_cases hb : b = 0
    · simp only [hb, hzero, map_zero]
    let B := (normForm q).polarBilin
    let j : Fin (n + 1) := ⟨1, by omega⟩
    have hij : (0 : Fin (n + 1)) ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      change 0 = 1 at hv
      omega
    obtain ⟨h, k, hh, hk, hcross⟩ := CFSGHyperbolicPrescribedGramPair.exists_pair
      (0 : Fin (n + 1)) j hij (-normForm q a) (-normForm q b) (-B a b)
    let P := slicePoint n q a ha h hh
    let R := slicePoint n q b hb k hk
    have hsrc : (fixedQuadraticForm n q).polarBilin
        (sliceVector n q h a) (sliceVector n q k b) = 0 := by
      rw [polar_parts, sliceVector_positive, sliceVector_negative,
        sliceVector_positive, sliceVector_negative, sliceVector_anisotropic,
        sliceVector_anisotropic, hcross]
      exact neg_add_cancel _
    have hz : ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val := by
      intro x hx y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp only [map_smul, LinearMap.smul_apply, hsrc, smul_zero]
    have himg := (horth P R).mpr hz
    have hv : sliceVector n q h (psi a) ∈ (f P).val := by
      rw [show (f P).val = Submodule.span (fixedField q) {sliceVector n q h (psi a)}
        from (hspec a ha).2 h hh]
      exact Submodule.mem_span_singleton_self _
    have hw : sliceVector n q k (psi b) ∈ (f R).val := by
      rw [show (f R).val = Submodule.span (fixedField q) {sliceVector n q k (psi b)}
        from (hspec b hb).2 k hk]
      exact Submodule.mem_span_singleton_self _
    have he := himg _ hv _ hw
    rw [polar_parts, sliceVector_positive, sliceVector_negative,
      sliceVector_positive, sliceVector_negative, sliceVector_anisotropic,
      sliceVector_anisotropic, hcross] at he
    exact add_left_cancel (he.trans (neg_add_cancel (B a b)).symm)

end SymmetricSubgroupAsymptotics.CFSGTwistedDSliceTailPairing
