import SymmetricSubgroupAsymptotics.CFSGTwistedAPairedFixedRoots

/-! The endpoint pair is genuinely orthogonal for every literal A rank
at least three. No rank-two adjacent pair is included. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

def endpointNode (s : ℕ) : Fin (s + 3) := ⟨0, by omega⟩

theorem endpointNode_cartan_zero (s : ℕ) :
    CartanMatrix.A (s + 3) (endpointNode s) (endpointNode s).rev = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, endpointNode, Fin.ext_iff,
    Fin.val_rev]
  change (if (0 : ℕ) = s + 3 - (0 + 1) then (2 : ℤ)
    else if 0 + 1 = s + 3 - (0 + 1) ∨ s + 3 - (0 + 1) + 1 = 0 then -1 else 0) = 0
  have hs : s + 3 - (0 + 1) = s + 2 := by omega
  rw [hs]
  have hd : (0 : ℕ) ≠ s + 2 := by omega
  have ha : ¬ (0 + 1 = s + 2 ∨ s + 2 + 1 = 0) := by omega
  simp only [if_neg hd, if_neg ha]

def endpointFixedRoot (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 2) :=
  pairedFixedRoot (s + 3) q neg (endpointNode s) (endpointNode_cartan_zero s) t

theorem endpointFixedRoot_toModel (s : ℕ) (q : CFSG.PrimePower)
    (neg : Bool) (t : q.Extension 2) :
    CFSGSerreFixedRootElements.fixedToModel (CartanMatrix.A (s + 3)) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order) (endpointFixedRoot s q neg t) =
        CFSGSerreModelRootGeneration.modelRoot (CartanMatrix.A (s + 3)) (q.Extension 2)
          neg (endpointNode s) t *
        CFSGSerreModelRootGeneration.modelRoot (CartanMatrix.A (s + 3)) (q.Extension 2)
          neg (endpointNode s).rev (t ^ q.order) := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
