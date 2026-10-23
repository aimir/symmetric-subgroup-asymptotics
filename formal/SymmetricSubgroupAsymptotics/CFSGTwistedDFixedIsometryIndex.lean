import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryFrameCover
import SymmetricSubgroupAsymptotics.CFSGTwistedDNormPlaneLiftWords
import SymmetricSubgroupAsymptotics.CFSGIndexFromPartialParameterCover
import SymmetricSubgroupAsymptotics.CFSGQuadraticSimilitudeGroup

/-! The full actual F-linear fixed-Q isometry group has literal
relative-root index at most four. The coset cover applies frame reduction
to the INVERSE isometry, preserving the one-sided order. No normality or
ambient K-linear recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryIndex
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDFixedIsometryFrameCover
open CFSGTwistedDNormIsometryParameters CFSGTwistedDNormPlaneLiftWords
open CFSGTwistedA2FixedField

abbrev fullIsometries (n : ℕ) (q : CFSG.PrimePower) :=
  CFSGQuadraticSimilitudeGroup.isometries (fixedQuadraticForm n q)

def relativeImage (n : ℕ) (q : CFSG.PrimePower) :
    Subgroup (fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q) := (fixedLinearHom n q).range

local instance (q : CFSG.PrimePower) : Finite (normIsometries q) :=
  Finite.of_injective (fun g : normIsometries q => (g.val : q.Extension 2 → q.Extension 2))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (fun x => congrFun h x)))

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Finite (fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q) :=
  Finite.of_injective (fun L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q =>
    (L : fixedSpace n q → fixedSpace n q)) (fun _ _ h => LinearEquiv.ext (fun x => congrFun h x))

theorem relativeImage_le_isometries (n : ℕ) (q : CFSG.PrimePower) :
    relativeImage n q ≤ fullIsometries n q := by
  rintro L ⟨g, rfl⟩
  exact fixedLinearHom_preserves_Q n q g

theorem inverse_residual_coset_cover (n : ℕ) (q : CFSG.PrimePower)
    (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q) (hL : L ∈ fullIsometries n q) :
    ∃ T : normIsometries q, (liftHom n q T)⁻¹ * L ∈ relativeImage n q := by
  have hQi (v) : fixedQuadraticForm n q (L.symm v) = fixedQuadraticForm n q v := by
    have h := hL (L.symm v)
    rw [L.apply_symm_apply] at h
    exact h.symm
  obtain ⟨g, T, hT, hres⟩ := exists_residual n q L.symm hQi
  let t : normIsometries q := ⟨T, hT⟩
  refine ⟨t⁻¹, ?_⟩
  rw [map_inv, inv_inv]
  refine ⟨g, ?_⟩
  apply LinearEquiv.ext
  intro v
  change fixedLinearHom n q g v = CFSGTwistedDNormPlaneLift.lift n q T (L v)
  simpa only [L.symm_apply_apply] using hres (L v)

theorem relative_index_le_four (n : ℕ) (q : CFSG.PrimePower) :
    ((relativeImage n q).subgroupOf (fullIsometries n q)).index ≤ 4 :=
  (CFSGIndexFromPartialParameterCover.index_le_of_partial_parameter_cover
    (relativeImage n q) (fullIsometries n q) (relativeImage_le_isometries n q)
    (liftHom n q) (retainedRotations q) (retained_lift_mem_range n q)
    (inverse_residual_coset_cover n q)).trans (retainedRotations_index_le_four q)

theorem isometries_card_le_four_mul_relative (n : ℕ) (q : CFSG.PrimePower) :
    Nat.card (CFSGQuadraticSimilitudeGroup.isometries (fixedQuadraticForm n q)) ≤
      4 * Nat.card (relativeRootGroup n q) := by
  let H := relativeImage n q
  let S := H.subgroupOf (fullIsometries n q)
  have hcard : Nat.card S = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (relativeImage_le_isometries n q)).toEquiv
  have hH : Nat.card H ≤ Nat.card (relativeRootGroup n q) :=
    Nat.card_le_card_of_surjective (fixedLinearHom n q).rangeRestrict
      (fixedLinearHom n q).rangeRestrict_surjective
  calc
    Nat.card (fullIsometries n q) = Nat.card S * S.index := S.card_mul_index.symm
    _ ≤ Nat.card S * 4 := Nat.mul_le_mul_left _ (relative_index_le_four n q)
    _ = Nat.card H * 4 := by rw [hcard]
    _ ≤ Nat.card (relativeRootGroup n q) * 4 := Nat.mul_le_mul_right _ hH
    _ = _ := Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryIndex
