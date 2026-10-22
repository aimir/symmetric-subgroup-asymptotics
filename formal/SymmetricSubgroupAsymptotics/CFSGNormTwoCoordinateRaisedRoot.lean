import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! A positively paired A2 step is an actual original norm-two lattice
root; it is constructed by its norm identity, not by root recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRaisedRoot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)

local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def raisedRoot (k : Roots A) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) : Roots A :=
  ⟨k.val+(s₀ i:Roots A).val,by
    simp only [map_add,LinearMap.add_apply]
    rw [k.property,hpair,integer_symmetric A hs (s₀ i:Roots A).val k.val,
      hpair,(s₀ i:Roots A).property]
    norm_num⟩

theorem raisedRoot_val (k : Roots A) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    (raisedRoot A hd hs hp ho k i hpair).val=k.val+(s₀ i:Roots A).val := rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRaisedRoot
