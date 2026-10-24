import SymmetricSubgroupAsymptotics.CFSGCubicTensorEnvelopeDimension
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact coordinates for the cubic semilinear tensor envelope. Its
distinguished slots read the two fixed scalars and two extension scalars
back directly, so no division by the orbit length is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGCubicTensorEnvelopeCoordinates

open CFSGCubicTensorEnvelopeDimension
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem tensorEmbedding_injective (W : Submodule F K) (sigma : K →ₗ[F] K) :
    Function.Injective (tensorEmbedding W sigma) := by
  intro p q hpq
  have h0 : p.1.val = q.1.val := congrFun hpq 0
  have h1 : p.2.1 = q.2.1 := congrFun hpq 1
  have h3 : p.2.2.1 = q.2.2.1 := congrFun hpq 3
  have h7 : p.2.2.2.val = q.2.2.2.val := congrFun hpq 7
  exact Prod.ext (Subtype.ext h0) (Prod.ext h1 (Prod.ext h3 (Subtype.ext h7)))

def tensorEnvelopeEquiv (W : Submodule F K) (sigma : K →ₗ[F] K) :
    (W × K × K × W) ≃ₗ[F] tensorEnvelope W sigma :=
  LinearEquiv.ofInjective (tensorEmbedding W sigma) (tensorEmbedding_injective W sigma)

theorem tensorEnvelope_finrank [FiniteDimensional F K]
    (W : Submodule F K) (sigma : K →ₗ[F] K) :
    Module.finrank F (tensorEnvelope W sigma) =
      2 * Module.finrank F W + 2 * Module.finrank F K := by
  rw [← (tensorEnvelopeEquiv W sigma).finrank_eq]
  simp only [Module.finrank_prod]
  omega

theorem tensorEnvelope_card (W : Submodule F K) (sigma : K →ₗ[F] K) :
    Nat.card (tensorEnvelope W sigma) = Nat.card W ^ 2 * Nat.card K ^ 2 := by
  rw [← Nat.card_congr (tensorEnvelopeEquiv W sigma).toEquiv]
  simp only [Nat.card_prod, pow_two]
  ac_rfl

end SymmetricSubgroupAsymptotics.CFSGCubicTensorEnvelopeCoordinates
