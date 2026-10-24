import SymmetricSubgroupAsymptotics.MatrixUnitBilinearIsometryOrderBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPositiveSpace
import SymmetricSubgroupAsymptotics.CFSGTwistedDOriginalOrderUpper
import Mathlib.Tactic.Ring

/-! Improved actual D and twisted-D order bounds. The ordinary group
preserves the literal split quadratic form; the twisted group acts
faithfully on its actual fixed-field space and preserves its literal
quadratic form. Both polar forms are already nondegenerate in every
characteristic. Central quotients are charged by actual surjections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearOrderUpper
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic

theorem elementaryProjective_card_le_bilinear_power (K : Type) [Field K] [Finite K]
    (s : ℕ) : Nat.card (elementaryProjective K (s+4)) ≤
      Nat.card K ^ (2*(s+4)^2+(s+4)) := by
  have hb := MatrixUnitBilinearIsometryOrderBound.central_quotient_card_le K
    (Index (s+4)) (elementaryRootGroup K (s+4))
    (splitQuadraticForm K (s+4)).polarBilin
    (splitQuadraticForm_nondegenerate K (s+4)) (by
      intro g x y
      change splitQuadraticForm K (s+4)
          ((g.val : Mat K (s+4)) *ᵥ x + (g.val : Mat K (s+4)) *ᵥ y) -
        splitQuadraticForm K (s+4) ((g.val : Mat K (s+4)) *ᵥ x) -
        splitQuadraticForm K (s+4) ((g.val : Mat K (s+4)) *ᵥ y) = _
      rw [← Matrix.mulVec_add, elementary_preserves_bundledQ,
        elementary_preserves_bundledQ, elementary_preserves_bundledQ]
      rfl)
  have hI : Nat.card (Index (s+4))=2*(s+4) := by
    simp only [Nat.card_sum, Nat.card_fin, two_mul]
  have he : (2*(s+4)*(2*(s+4)+1))/2 = 2*(s+4)^2+(s+4) := by
    symm
    apply Nat.eq_div_of_mul_eq_right (by decide : (2:ℕ)≠0)
    ring
  simpa only [hI, he] using hb

theorem typeD_order_le_bilinear_power (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)] :
    Nat.card (CFSG.Models.D r q)≤q.order^(2*r^2+r) := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  let e := serreProjectiveEquivElementaryProjective q.Field s
  rw [Nat.card_congr e.toEquiv]
  simpa only [q.card_field] using elementaryProjective_card_le_bilinear_power q.Field s

open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDFixedQuadraticNondegenerate CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDRelativeProjectiveModel CFSGTwistedA2FixedField

theorem relative_card_le_bilinear_power (n : ℕ) (q : CFSG.PrimePower) :
    Nat.card (relativeRootGroup n q)≤q.order^(2*(n+2)^2+(n+2)) := by
  letI : Finite (fixedSpace n q) := Finite.of_injective
    (fun v : fixedSpace n q => v.val) Subtype.val_injective
  have hb := FiniteBilinearIsometryOrderBound.card_le_pow_finrank
    (fixedLinearHom n q) (fixedLinearHom_injective n q)
    (fixedQuadraticForm n q).polarBilin (fixedQuadraticForm_nondegenerate n q) (by
      intro g x y
      change fixedQuadraticForm n q (fixedLinearHom n q g x + fixedLinearHom n q g y) -
        fixedQuadraticForm n q (fixedLinearHom n q g x) -
        fixedQuadraticForm n q (fixedLinearHom n q g y) = _
      rw [← map_add, fixedLinearHom_preserves_Q, fixedLinearHom_preserves_Q,
        fixedLinearHom_preserves_Q]
      rfl)
  rw [fixedField_card, CFSGTwistedDOriginalOrderUpper.fixedSpace_finrank] at hb
  have he : (2*(n+2)*(2*(n+2)+1))/2 = 2*(n+2)^2+(n+2) := by
    symm
    apply Nat.eq_div_of_mul_eq_right (by decide : (2:ℕ)≠0)
    ring
  simpa only [he] using hb

theorem typeTwistedD_order_le_bilinear_power (r : ℕ) (hr : 4≤r)
    (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedD r q)] :
    Nat.card (CFSG.Models.TwistedD r q)≤q.order^(2*r^2+r) := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  let e := originalRelativeProjectiveEquiv s q
  rw [Nat.card_congr e.toEquiv]
  calc
    Nat.card (relativeRootGroup (s+2) q ⧸ Subgroup.center (relativeRootGroup (s+2) q)) ≤
        Nat.card (relativeRootGroup (s+2) q) :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center _))
        (QuotientGroup.mk'_surjective _)
    _ ≤ q.order^(2*(s+4)^2+(s+4)) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using relative_card_le_bilinear_power (s+2) q

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearOrderUpper
