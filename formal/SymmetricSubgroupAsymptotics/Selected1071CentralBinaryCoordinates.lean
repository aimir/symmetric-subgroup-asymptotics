import SymmetricSubgroupAsymptotics.Selected1071OriginalKernel
import Mathlib.Data.ZMod.Basic

/-! Two literal binary coordinates on the SAME original central kernel,
read from its action on original point zero. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph

private def pointBits (p : Equiv.Perm (Fin 16)) (j : Fin 2) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (((p 0).val / 2^j.val : ℕ) : ZMod 2)

private theorem pointBits_mul : ∀ (i j : Fin 4) (a : Fin 2),
    pointBits (kernelElements i*kernelElements j) a=
      pointBits (kernelElements i) a*pointBits (kernelElements j) a := by decide +kernel

private theorem pointBits_separates : ∀ (i j : Fin 4),
    (∀ a : Fin 2, pointBits (kernelElements i) a=pointBits (kernelElements j) a) → i=j := by
  decide +kernel

def centralBinaryCoordinates : originalKernel →* (Fin 2 → Multiplicative (ZMod 2)) where
  toFun z := pointBits ((z : Original) : Equiv.Perm (Fin 16))
  map_one' := by
    funext j
    change pointBits 1 j=1
    revert j
    decide +kernel
  map_mul' z w := by
    obtain ⟨i,hi⟩ := z.property
    obtain ⟨j,hj⟩ := w.property
    funext a
    change pointBits (((z : Original) : Equiv.Perm (Fin 16))*
      ((w : Original) : Equiv.Perm (Fin 16))) a=
      pointBits ((z : Original) : Equiv.Perm (Fin 16)) a*
        pointBits ((w : Original) : Equiv.Perm (Fin 16)) a
    rw [hi,hj]
    exact pointBits_mul i j a

theorem centralBinaryCoordinates_injective : Function.Injective centralBinaryCoordinates := by
  intro z w h
  obtain ⟨i,hi⟩ := z.property
  obtain ⟨j,hj⟩ := w.property
  have hij : i=j := pointBits_separates i j (by
    intro a
    have ha := congrFun h a
    change pointBits ((z : Original) : Equiv.Perm (Fin 16)) a=
      pointBits ((w : Original) : Equiv.Perm (Fin 16)) a at ha
    simpa only [hi,hj] using ha)
  apply Subtype.ext
  apply Subtype.ext
  exact hi.trans ((congrArg kernelElements hij).trans hj.symm)

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
