import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement

/-! Opaque range membership for actual selected root elements. Later
normalizer/quotient proofs can use this without unfolding the chosen
rootWitness and its complete integral matrix data during elaboration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootElement
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho

theorem mem_rootSubgroup_iff_selected (K : Type) [Field K] (k : Roots A)
    (x : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) :
    x∈rootSubgroup A hd hs hp ho K k↔∃a : K,selectedRootElement A hd hs hp ho K k a=x :=
  mem_wordRootSubgroup_iff A hd hs hp ho K
    (rootWitness A hd hs hp ho k).val.1 (rootWitness A hd hs hp ho k).val.2 x

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange
