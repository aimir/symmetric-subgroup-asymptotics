import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration

/-! Actual termination of the positive-root height filtration, uniformly
in coefficient characteristic. The bound is computed from the FINITE
original lattice root set, not supplied as an extra model hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightBound
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateRootHeightFiltration

def rootHeightBound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) [Fintype (Roots A)] : ℕ :=
  open scoped Classical in Finset.univ.sup (fun k : Roots A=>(height k.val).natAbs)

theorem height_le_rootHeightBound {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) [Fintype (Roots A)]
    (k : Roots A) : height k.val≤(rootHeightBound A:ℤ) := by
  classical
  have hn : (height k.val).natAbs≤rootHeightBound A :=
    Finset.le_sup (f:=fun k : Roots A=>(height k.val).natAbs) (Finset.mem_univ k)
  have hcast : ((height k.val).natAbs:ℤ)≤(rootHeightBound A:ℤ) := by exact_mod_cast hn
  exact Int.le_natAbs.trans hcast

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem final_heightTail_eq_bot (K : Type) [Field K] :
    heightTail A hd hs hp ho K ((rootHeightBound A:ℤ)+1)=⊥ := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨k,hk,a,rfl⟩
    have hb := height_le_rootHeightBound A k.val
    omega
  · exact bot_le

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightBound
