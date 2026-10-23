import SymmetricSubgroupAsymptotics.CFSGTwistedDSliceCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicProjectionCoupling

/-! Actual image rays on a fixed nonzero anisotropic slice have a
representative with EXACTLY the original hyperbolic projection, and its
anisotropic tail is unique. Both projection scalars are the single scalar
proved on actual mixed planes; no preservation of the slice is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedSliceImages
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedDSliceCoordinates
open CFSGTwistedDHyperbolicProjectionCoupling CFSGTwistedDLinearParameters
open CFSGTwistedA2FixedField CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem level_vector_nonzero (n : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) (ha : a ≠ 0)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hlevel : dotProduct h.1 h.2 = -normForm q a) : h ≠ 0 := by
  intro he
  have hp : h.1 = 0 := congrArg Prod.fst he
  rw [hp, zero_dotProduct] at hlevel
  exact (neg_ne_zero.mpr (normForm_ne_zero q ha)) hlevel.symm

def slicePoint (n : ℕ) (q : CFSG.PrimePower) (a : q.Extension 2) (ha : a ≠ 0)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hlevel : dotProduct h.1 h.2 = -normForm q a) : Points (fixedQuadraticForm n q) :=
  ray (fixedQuadraticForm n q) (sliceVector n q h a)
    (sliceVector_nonzero n q h a (level_vector_nonzero n q a ha h hlevel))
    (by rw [quadratic_sliceVector, hlevel, neg_add_cancel])

def NormalizedImage (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (a : q.Extension 2) (ha : a ≠ 0)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hlevel : dotProduct h.1 h.2 = -normForm q a) (b : q.Extension 2) : Prop :=
  (f (slicePoint n q a ha h hlevel)).val = Submodule.span (fixedField q) {sliceVector n q h b}

theorem exists_normalized_image (n : ℕ) (q : CFSG.PrimePower) (hn : 1 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (horth : ∀ P R, ZeroOn (fixedQuadraticForm n q).polarBilin (f P).val (f R).val ↔
      ZeroOn (fixedQuadraticForm n q).polarBilin P.val R.val)
    (hfix : ∀ P : Points (fixedQuadraticForm n q),
      (∀ v ∈ P.val, anisotropicPart n q v = 0) → f P = P)
    (a : q.Extension 2) (ha : a ≠ 0)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hlevel : dotProduct h.1 h.2 = -normForm q a) :
    ∃ b, NormalizedImage n q f a ha h hlevel b := by
  let A := fixedQuadraticForm n q
  let P := slicePoint n q a ha h hlevel
  let v := sliceVector n q h a
  have hv : v ∈ P.val := Submodule.mem_span_singleton_self _
  have hv0 : v ≠ 0 := sliceVector_nonzero n q h a (level_vector_nonzero n q a ha h hlevel)
  obtain ⟨w, hw, hw0⟩ := point_nonzero A (f P)
  have hxy : dotProduct (positivePart n q v) (negativePart n q v) ≠ 0 := by
    dsimp only [v]
    rw [sliceVector_positive, sliceVector_negative, hlevel]
    exact neg_ne_zero.mpr (normForm_ne_zero q ha)
  obtain ⟨c, hc, hp, hm⟩ := paired_projections_common_scalar n q hn f horth hfix
    P v w hv hw hv0 hw0 hxy
  let z := c⁻¹ • w
  let b := anisotropicPart n q z
  have hzP : positivePart n q z = h.1 := by
    change positivePart n q (c⁻¹ • w) = h.1
    rw [map_smul, hp, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact sliceVector_positive n q h a
  have hzN : negativePart n q z = h.2 := by
    change negativePart n q (c⁻¹ • w) = h.2
    rw [map_smul, hm, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact sliceVector_negative n q h a
  have hz : z = sliceVector n q h b := by
    apply (linearParameters n q).injective
    rw [sliceVector_parameters]
    exact Prod.ext hzP (Prod.ext hzN rfl)
  refine ⟨b, ?_⟩
  change (f P).val = Submodule.span (fixedField q) {sliceVector n q h b}
  calc
    (f P).val = Submodule.span (fixedField q) {w} := (point_span A (f P) w hw hw0).symm
    _ = Submodule.span (fixedField q) {z} :=
      (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)) w).symm
    _ = Submodule.span (fixedField q) {sliceVector n q h b} := congrArg (fun x => Submodule.span (fixedField q) {x}) hz

theorem normalized_image_unique (n : ℕ) (q : CFSG.PrimePower)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (a : q.Extension 2) (ha : a ≠ 0)
    (h : (Fin (n + 1) → fixedField q) × (Fin (n + 1) → fixedField q))
    (hlevel : dotProduct h.1 h.2 = -normForm q a) (b c : q.Extension 2)
    (hb : NormalizedImage n q f a ha h hlevel b)
    (hc : NormalizedImage n q f a ha h hlevel c) : b = c :=
  span_sliceVector_unique n q h (level_vector_nonzero n q a ha h hlevel) b c (hb.symm.trans hc)

end SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedSliceImages
