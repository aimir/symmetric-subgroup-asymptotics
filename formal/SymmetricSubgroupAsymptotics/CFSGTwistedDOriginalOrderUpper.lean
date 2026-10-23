import SymmetricSubgroupAsymptotics.FiniteLinearActionOrderBound
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedQuadraticAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel

/-! The ORIGINAL twisted-D model has the honest q^(4r²) matrix-space
upper bound over the ACTUAL fixed field. The relative group already
acts faithfully on its defining-fixed vector space of dimension2r. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOriginalOrderUpper
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeProjectiveModel
open CFSGTwistedA2FixedField CFSGOrthogonalDSerreMatrices

theorem fixedSpace_finrank (n : ℕ) (q : CFSG.PrimePower) :
    Module.finrank (fixedField q) (fixedSpace n q)=2*(n+2) := by
  letI : Finite (fixedSpace n q) := Finite.of_injective
    (fun v : fixedSpace n q=>v.val) Subtype.val_injective
  apply Nat.pow_right_injective (CFSGTwistedAQuadraticTrace.order_two_le q)
  have hc := Module.natCard_eq_pow_finrank (K:=fixedField q) (V:=fixedSpace n q)
  rw [fixedSpace_card,fixedField_card] at hc
  exact hc.symm

theorem relative_card_le_fixed_matrix_power (n : ℕ) (q : CFSG.PrimePower) :
    Nat.card (relativeRootGroup n q)≤q.order^(4*(n+2)^2) := by
  letI : Finite (fixedSpace n q) := Finite.of_injective
    (fun v : fixedSpace n q=>v.val) Subtype.val_injective
  have hb := FiniteLinearActionOrderBound.card_le_pow_finrank_square
    (fixedField q) (fixedSpace n q) (fixedLinearHom n q) (fixedLinearHom_injective n q)
  rw [fixedField_card,fixedSpace_finrank] at hb
  convert hb using 1 <;> congr 1 <;> ring

theorem typeTwistedD_order_le_fixed_matrix_power (r : ℕ) (hr : 4≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD r q)] :
    Nat.card (CFSG.Models.TwistedD r q)≤q.order^(4*r^2) := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+4 := ⟨r-4,by omega⟩
  let e := originalRelativeProjectiveEquiv s q
  rw [Nat.card_congr e.toEquiv]
  calc
    Nat.card (relativeRootGroup (s+2) q ⧸Subgroup.center (relativeRootGroup (s+2) q))≤
        Nat.card (relativeRootGroup (s+2) q) :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center (relativeRootGroup (s+2) q)))
        (QuotientGroup.mk'_surjective _)
    _ ≤q.order^(4*(s+4)^2) := by
      simpa only [Nat.add_assoc,Nat.reduceAdd] using relative_card_le_fixed_matrix_power (s+2) q

end SymmetricSubgroupAsymptotics.CFSGTwistedDOriginalOrderUpper
