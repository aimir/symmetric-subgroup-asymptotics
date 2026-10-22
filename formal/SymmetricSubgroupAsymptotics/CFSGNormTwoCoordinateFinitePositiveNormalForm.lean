import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootParameterEquiv
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality

/-! A genuine unique ordered-height normal form for the actual Geck U
over FINITE fields. Surjectivity is the checked actual collection theorem;
injectivity follows from the exact cardinality proved by unique layer
factorization, not from a normal-form or group-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFinitePositiveNormalForm
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinatePositiveHeightNormalForm CFSGNormTwoCoordinatePositiveCardinality
open CFSGNormTwoCoordinateRootParameterEquiv
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

def positiveRootNormalWord (K : Type) [Field K] (c : PositiveRoot A→K) :
    PositiveGroup A hd hs hp ho K :=
  positiveHeightNormalWord A hd hs hp ho K (rootParameterEquiv A K c)

theorem positiveRootNormalWord_surjective (K : Type) [Field K] :
    Function.Surjective (positiveRootNormalWord A hd hs hp ho K) :=
  (positiveHeightNormalWord_surjective A hd hs hp ho K).comp (rootParameterEquiv A K).surjective

theorem positiveRootNormalWord_bijective (K : Type) [Field K] [Finite K] :
    Function.Bijective (positiveRootNormalWord A hd hs hp ho K) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨positiveRootNormalWord_surjective A hd hs hp ho K,?_⟩
  rw [Nat.card_fun,positive_card]

def positiveRootNormalEquiv (K : Type) [Field K] [Finite K] :
    (PositiveRoot A→K) ≃ PositiveGroup A hd hs hp ho K :=
  Equiv.ofBijective _ (positiveRootNormalWord_bijective A hd hs hp ho K)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFinitePositiveNormalForm
