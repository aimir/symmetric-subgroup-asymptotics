import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.BoundedComponentSocleClassNumerics

/-! A proved order-at-index packet supplies a class packet on the SAME
simple factor. The checked power-66 scalar is specialized at each actual
proper index; the subsequent adapter chooses the actual least index.
No fixed-1024/2048 bound on the component order is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallFibreLargeIndexOrderClassResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_gap_or_least_short_index_of_order_index_power
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (hindex : ∀ K : Subgroup E.Simple, K ≠ ⊤ → 1024 ≤ K.index)
    (horder : ∀ K : Subgroup E.Simple, K ≠ ⊤ →
      Nat.card E.Simple*Nat.card (Outer E.Simple) ≤ K.index^66)
    (hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2 < Nat.card E.Simple)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (E.factorCount=1 ∧ ∃ ell : ℕ, LeastProperIndex E.Simple ell ∧
        ∃ K : Subgroup E.Simple, K ≠ ⊤ ∧ Nat.card X=K.index ∧
          ell ≤ K.index ∧ K.index < 2*ell+2) := by
  apply SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
    π hπ c hc hsize E ?_ hsquare H hH
  intro K hK
  have hi := hindex K hK
  have hn := BoundedComponentSocleClassNumerics.component_cube_le_garonziMaroti
    K.index 1 (by omega) (by decide) (by simpa only [pow_one] using hi)
  simp only [pow_one,Nat.factorial_one,mul_one] at hn
  have hclass : Nat.card (ConjClasses E.Simple) ≤ Nat.card E.Simple :=
    Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
  exact (((Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hclass) 3).trans
    (Nat.pow_le_pow_left (horder K hK) 3)).trans hn).trans
      (Nat.pow_le_pow_right (by decide) (by omega : K.index-1 ≤ K.index+1))

end SymmetricSubgroupAsymptotics.SmallFibreLargeIndexOrderClassResidual
