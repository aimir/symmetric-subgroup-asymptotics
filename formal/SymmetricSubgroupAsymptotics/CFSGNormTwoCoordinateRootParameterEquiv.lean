import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightPartition
import Mathlib.Logic.Equiv.Basic

/-! The SAME independent positive-root parameters can be indexed either
by roots or by all natural height layers. No parameters occur beyond
the actual finite root heights, although no explicit census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootParameterEquiv
open CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateRootHeightCommutator
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) [Fintype (Roots A)]

def allHeightRootEquiv :
    (Σn : ℕ,ExactHeightRoot A ((n:ℤ)+1)) ≃ PositiveRoot A :=
  Equiv.ofBijective (fun p=>p.2.val) (by
    constructor
    · rintro ⟨n,k⟩ ⟨m,l⟩ he
      have hnm : n=m := by
        have hh := congrArg (fun t : PositiveRoot A=>height t.val.val) he
        dsimp only at hh
        rw [k.property,l.property] at hh
        omega
      cases hnm
      have hkl : k=l := Subtype.ext he
      cases hkl
      rfl
    · intro k
      have hp := positive_root_height_pos A k.val k.property
      have hc : ((height k.val.val).toNat:ℤ)=height k.val.val := Int.toNat_of_nonneg (by omega)
      refine ⟨⟨(height k.val.val).toNat-1,⟨k,by omega⟩⟩,rfl⟩)

def rootParameterEquiv (K : Type*) :
    (PositiveRoot A→K) ≃ (∀n : ℕ,ExactHeightRoot A ((n:ℤ)+1)→K) :=
  ((Equiv.arrowCongr (allHeightRootEquiv A) (Equiv.refl K)).symm).trans
    (Equiv.piCurry (fun (n : ℕ) (_ : ExactHeightRoot A ((n:ℤ)+1))=>K))

theorem rootParameterEquiv_apply (K : Type*) (c : PositiveRoot A→K)
    (n : ℕ) (k : ExactHeightRoot A ((n:ℤ)+1)) :
    rootParameterEquiv A K c n k=c k.val := rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootParameterEquiv
