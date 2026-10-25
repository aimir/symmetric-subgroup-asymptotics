import SymmetricSubgroupAsymptotics.CFSGFFourBinaryLeviNativePointCoordinates
import Mathlib.LinearAlgebra.Prod

/-! The faithful native symplectic point-lift action on the literal
seven central coordinates. This constructs the acting homomorphism;
its actual F4 lifts are established separately for displayed generators,
without surjectivity onto the native symplectic group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourBinaryNativeCentralAction
open CFSGFFourBinaryRadicalCentralLayers CFSGFFourBinaryLeviNativeVectorCoordinates
open CFSGFFourBinaryLeviNativePointCoordinates CFSGFFourBinaryShortLeviCentralAction
open CFSGFFourBinaryLongLeviCentralAction CFSGSymplecticSerreMatrices
open CFSGSymplecticBinaryPointTailAction CFSGSymplecticHeisenbergVectorAction
variable (K : Type) [Field K] [Finite K] [CharP K 2]
private abbrev Vector := (Fin 3 → K) × (Fin 3 → K)
private abbrev Raw := K × Vector K
private def reorder : (Vector K × K) ≃ₗ[K] Raw K := LinearEquiv.prodComm K (Vector K) K

def nativeCentralAction (hK : Nat.card K=2) : elementaryRootGroup K 3 →* MulAut (CentralCoordinates K) where
  toFun A := AddEquiv.toMultiplicative
    ((((reorder K).symm.trans (pointLinearHom K hK 3 A)).trans (reorder K)).toAddEquiv)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    change reorder K (pointLinearHom K hK 3 1 ((reorder K).symm x.toAdd)) = x.toAdd
    rw [map_one]
    exact (reorder K).apply_symm_apply x.toAdd
  map_mul' A B := by
    apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    change reorder K (pointLinearHom K hK 3 (A*B) ((reorder K).symm x.toAdd)) =
      reorder K (pointLinearHom K hK 3 A ((reorder K).symm
        (reorder K (pointLinearHom K hK 3 B ((reorder K).symm x.toAdd)))))
    rw [(reorder K).symm_apply_apply,map_mul]
    rfl

theorem nativeCentralAction_apply (hK : Nat.card K=2) (A : elementaryRootGroup K 3)
    (x : CentralCoordinates K) :
    nativeCentralAction K hK A x = Multiplicative.ofAdd
      (let y := pointLinearHom K hK 3 A (x.toAdd.2,x.toAdd.1); (y.2,y.1)) := rfl

theorem nativeCentralAction_injective (hK : Nat.card K=2) :
    Function.Injective (nativeCentralAction K hK) := by
  intro A B h
  have hv (v : Vector K) : vectorLinearHom K 3 A v = vectorLinearHom K 3 B v := by
    have hx := congrArg (fun f : MulAut (CentralCoordinates K) =>
      (f (Multiplicative.ofAdd (0,v))).toAdd.2) h
    change (pointLinearHom K hK 3 A (v,0)).1 = (pointLinearHom K hK 3 B (v,0)).1 at hx
    exact hx
  apply CFSGSymplecticHeisenbergWords.elementary_ext_of_mulVec K 3 A B
  intro w
  have he := hv ((vectorEquiv K 3).symm w)
  rw [vectorLinearHom_apply,vectorLinearHom_apply] at he
  have hw := (vectorEquiv K 3).symm.injective he
  rw [(vectorEquiv K 3).apply_symm_apply] at hw
  exact hw

theorem nativeCentralAction_short (hK : Nat.card K=2) (n : Fin 2) (a : K)
    (x : CentralCoordinates K) :
    nativeCentralAction K hK (nativePositive K n.castSucc a) x = shortShear K n a x := by
  apply Multiplicative.toAdd.injective
  exact native_short_point K hK n a x.toAdd

theorem nativeCentralAction_long (hK : Nat.card K=2) (a : K) (x : CentralCoordinates K) :
    nativeCentralAction K hK (nativePositive K 2 a) x = longShear K a x := by
  apply Multiplicative.toAdd.injective
  exact native_long_point K hK a x.toAdd

end SymmetricSubgroupAsymptotics.CFSGFFourBinaryNativeCentralAction
