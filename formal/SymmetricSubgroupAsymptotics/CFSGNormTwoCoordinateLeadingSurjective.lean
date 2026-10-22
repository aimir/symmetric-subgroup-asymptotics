import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! Every coordinate vector occurs in the actual first simple-root
layer: the already-proved ordered simple word has those coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingSurjective
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoGeckOrderedSimpleFactor CFSGNormTwoGeckIntegralRealization
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem leadingHom_surjective (K : Type) [Field K] :
    Function.Surjective (leadingHom A hd hs hp ho K) := by
  intro c
  let q := orderedSimple A hs hp b₀ s₀ K c.toAdd
  have hq := orderedSimple_mem_positive A hs hp b₀ s₀ K c.toAdd
  have hc := leading_factor_unique A hd hs hp ho K q 1 hq
    (CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp b₀ s₀ K false).one_mem
    (by intro i j hij;rfl) c.toAdd (by simp only [q,one_mul])
  refine ⟨⟨q,hq⟩,?_⟩
  change Multiplicative.ofAdd (leadingCoordinates A hd hs hp ho K q)=c
  rw [←hc]
  rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingSurjective
