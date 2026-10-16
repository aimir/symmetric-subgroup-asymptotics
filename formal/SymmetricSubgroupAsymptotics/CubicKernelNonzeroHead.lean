import SymmetricSubgroupAsymptotics.CubicElementaryKernelCoordinates
import SymmetricSubgroupAsymptotics.ScalarFourDoubleHeadJointCount

/-! A surviving scalar coordinate converts the actual cubic kernel chart
into the joint headed target interface. Only actual maps are inputs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace CubicKernelNonzeroHead
open CubicElementaryKernelCoordinates

variable {Q V : Type} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  (top : Q →* CyclicThree) (htop : Function.Surjective top)
  (rho : Representation (ZMod 2) CyclicThree V)
  (e : top.ker ≃* Multiplicative V) (D : CubicBinaryCoordinates rho)
  (hconj : ∀ q p, e (MulAut.conjNormal q p) =
    Multiplicative.ofAdd (rho (top q) (Multiplicative.toAdd (e p))))

/-- Two scalar coordinates are reindexed so the surviving one is first;
the invariant coordinates and original group/kernel stay literal. -/
def jointData (j : Fin 2)
    (hne : ∃ p : top.ker, scalar top rho e D j p ≠ 1) :
    ScalarFourDoubleHeadJointData Q := by
  let s := scalar top rho e D
  let a := invariant top rho e D
  let perm : Equiv.Perm (Fin 2) := Equiv.swap 0 j
  let C : Subgroup top.ker := (s 0).ker ⊓ (s 1).ker
  have hC : ∀ z ∈ C, ∀ k : Fin 2, s k z = 1 := by
    intro z hz k
    fin_cases k
    · exact MonoidHom.mem_ker.mp hz.1
    · exact MonoidHom.mem_ker.mp hz.2
  let h : ScalarFourHeadedQuotient Q :=
    { top := top
      top_surjective := htop
      center := C
      center_comm := by
        intro z _ p
        apply e.injective
        rw [map_mul,map_mul,mul_comm]
      center_twoGroup :=
        ((ZModModule.isPGroup_multiplicative (n := 2) (G := V)).of_injective
          e.toMonoidHom e.injective).of_injective C.subtype Subtype.val_injective
      layers := 1
      coord := fun k => s (perm k)
      coord_center := by intro k z hz; exact hC z hz (perm k)
      coord_joint := by
        intro p hp
        constructor
        · apply MonoidHom.mem_ker.mpr
          simpa only [Equiv.apply_symm_apply] using hp (perm.symm 0)
        · apply MonoidHom.mem_ker.mpr
          simpa only [Equiv.apply_symm_apply] using hp (perm.symm 1)
      coord_twisted := by
        intro q p k
        exact scalar_conj top rho e D hconj q p (perm k)
      coord_zero_surjective := by
        have hj : perm 0 = j := Equiv.swap_apply_left 0 j
        change Function.Surjective (s (perm 0))
        rw [hj]
        exact scalar_surjective top rho e D hconj htop j hne }
  refine
    { headed := h
      first := perm.symm 0
      second := perm.symm 1
      invariant := a
      invariant_conj := by
        intro q p k
        exact CubicElementaryKernelCoordinates.invariant_conj top rho e D hconj q p k
      joint := ?_ }
  intro p q he
  apply CubicElementaryKernelCoordinates.joint top rho e D
  simpa only [h,Equiv.apply_symm_apply] using he

end CubicKernelNonzeroHead
end SymmetricSubgroupAsymptotics
end
