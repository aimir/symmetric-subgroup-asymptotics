import SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameReindex
import Mathlib.Data.Fintype.EquivFin

/-! The previously bounded frame stabilizer consists exactly of the
literal coordinate field automorphisms. Surjectivity follows from the
actual injection and the already-proved finite cardinal bound. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
open CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem frameMap_injective (b i j : n) (hij : i ≠ j) :
    Function.Injective (frameMap (F := F) b) := by
  intro s t he
  ext a
  let v : n → F := Pi.single i 1 + Pi.single j a
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrFun hz i
    simp [v, Pi.single_apply, hij] at hh
  have hp := congrArg (fun f : frameStabilizer (F := F) b =>
    f.val.val (Projectivization.mk F v hv)) he
  change pointEquiv s (Projectivization.mk F v hv) =
    pointEquiv t (Projectivization.mk F v hv) at hp
  rw [pointEquiv_mk, pointEquiv_mk] at hp
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hp
  have hc1 : (c : F) = 1 := by
    have hh := congrFun hc i
    simpa [v, Pi.single_apply, hij, Function.comp_apply, Pi.smul_apply,
      Units.smul_def] using hh
  have ha := congrFun hc j
  simpa [v, Pi.single_apply, hij.symm, Function.comp_apply, Pi.smul_apply,
    Units.smul_def, hc1] using ha.symm

theorem frameMap_surjective [Finite F] (b i j : n)
    (hbi : b ≠ i) (hbj : b ≠ j) (hij : i ≠ j) :
    Function.Surjective (frameMap (F := F) b) := by
  letI : Finite (F ≃+* F) := Finite.of_injective
    (fun s : F ≃+* F => (s : F → F)) DFunLike.coe_injective
  letI : Fintype (F ≃+* F) := Fintype.ofFinite _
  letI : Fintype (frameStabilizer (F := F) b) := Fintype.ofFinite _
  apply ((Fintype.bijective_iff_injective_and_card (frameMap (F := F) b)).mpr ?_).surjective
  refine ⟨frameMap_injective b i j hij, ?_⟩
  apply le_antisymm
  · exact Fintype.card_le_of_injective _ (frameMap_injective b i j hij)
  · simpa only [Nat.card_eq_fintype_card] using
      frameStabilizer_card_le_of_three_coordinates (F := F) b i j hbi hbj hij

end SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
