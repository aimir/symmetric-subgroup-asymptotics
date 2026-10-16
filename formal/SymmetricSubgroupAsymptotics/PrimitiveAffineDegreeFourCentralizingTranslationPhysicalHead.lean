import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalCubicFixedFibreChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalTranslationMovingFibreChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineOriginalTranslationCoordinateIdentity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalLocalFaithfulnessEveryBlock
import SymmetricSubgroupAsymptotics.BinaryCubicFixedFibreCentralizer
import SymmetricSubgroupAsymptotics.BinaryFourCubicMovingFibreDetection
import SymmetricSubgroupAsymptotics.BinaryFourCubicNormalizerShapeHead
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The positive fixed-translation branch on the original sixteen physical
points. Both fibre charts and the nonzero moving coordinate are constructed;
the original outer stabilizer epimorphism and local plane remain unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourBlockAugmentation BinaryFourCubicNormalizerPointShapes

variable {U : PreE7NonPairActionClass 16} {basePoint : Fin 16}
    (block : OriginalMinimalBlock (A := preE7NonPairAction 16 U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

private def labelFibre (d : block.Points ≃ Fin 4) (j : Fin 4) :
    originalBlockFibre block.map (d.symm j) ≃
      {x : Fin 16 // d (block.map x) = j} :=
  Equiv.subtypeEquivRight (fun x => by
    constructor
    · intro h
      rw [h,d.apply_symm_apply]
    · intro h
      apply d.injective
      exact h.trans (d.apply_symm_apply j).symm)

private theorem physical_head
    (hr : Nat.card block.Fibre = 4)
    (S : Sylow 3 (preE7NonPairAction 16 U)) (s : preE7NonPairAction 16 U)
    (d : block.Points ≃ Fin 4)
    (hgen : (S : Subgroup (preE7NonPairAction 16 U)) = Subgroup.zpowers s)
    (hs3 : s^3 = 1) (hsq : QuotientGroup.mk' (E block P) s ≠ 1)
    (hd : ∀ i : block.Points, d (s • i) = blockCycle (d i))
    (hlocal : Function.Injective (binaryAffineStabilizerComponent block P (d.symm 0)))
    (z : E block P) (hzne : (z : preE7NonPairAction 16 U) ≠ 1)
    (hz : (z : preE7NonPairAction 16 U) ∈
      Subgroup.centralizer (S : Set (preE7NonPairAction 16 U)))
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (f : MulAction.stabilizer (preE7NonPairAction 16 U) x →* L)
    (hf : Function.Surjective f) (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction 16 U) x).subtype
        (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (preE7NonPairAction 16 U) (ZMod 2))) ≤ 6 := by
  have hsS : s ∈ (S : Subgroup (preE7NonPairAction 16 U)) := by
    rw [hgen]
    exact Subgroup.mem_zpowers s
  have hcommute (y : Fin 16) :
      (z : preE7NonPairAction 16 U) • (s • y) =
        s • ((z : preE7NonPairAction 16 U) • y) := by
    simpa only [mul_smul] using congrArg
      (fun g : preE7NonPairAction 16 U => g • y) (hz s hsS).symm
  have hsi : s • d.symm 0 = d.symm 0 := by
    apply d.injective
    rw [hd,d.apply_symm_apply]
    decide +kernel
  obtain ⟨a,ha⟩ := originalCubicFixedFibreChart block P hr (d.symm 0)
    s hsi hs3 hsq hlocal
  let fixed := a.trans (labelFibre block d 0)
  let moving := originalRawLabelledFibreChart block hr d 1
  let pi : Fin 16 → Fin 4 := fun y => d (block.map y)
  have hfixedAction (v : Local) : (fixed (localCycle v)).1 = s • (fixed v).1 := ha v
  have hpi (y : Fin 16) : pi (s • y) = blockCycle (pi y) := by
    change d (block.map (s • y)) = blockCycle (d (block.map y))
    rw [block.map_equivariant,hd]
  have hz2 : (z : preE7NonPairAction 16 U)^2 = 1 :=
    congrArg Subtype.val (degreeFour_translation_pow_two block P hr z)
  have hzpreserve (y : Fin 16) (hy : pi y = 0) :
      pi ((z : preE7NonPairAction 16 U) • y) = 0 := by
    change d (block.map ((z : preE7NonPairAction 16 U) • y)) = 0
    rw [block.map_equivariant,originalTranslation_fixes_blocks block P z]
    exact hy
  have hzfixed : ∀ v : Local, (z : preE7NonPairAction 16 U) • (fixed v).1 =
      (fixed v).1 := BinaryCubicFixedFibreCentralizer.actual_fibre_fixed
    (fun y => pi y = 0) fixed s z hfixedAction hzpreserve hz2 hcommute
  have hmove := BinaryFourCubicMovingFibreDetection.exists_moving
    pi s fixed moving hpi (by simp) z hzne hcommute hzfixed
  have hcoord : (ambientEmbedding block (z : preE7NonPairAction 16 U)).left (d.symm 1) ≠ 1 := by
    intro hzero
    obtain ⟨v,hv⟩ := hmove
    apply hv
    apply originalTranslationCoordinate_identity_fixes_fibre block P z (d.symm 1)
      hzero (moving v).1
    apply d.injective
    exact (moving v).2.trans (d.apply_symm_apply 1).symm
  obtain ⟨b,hb⟩ := originalTranslationMovingFibreChart block P hr (d.symm 1) z hcoord
  let moving' := b.trans (labelFibre block d 1)
  let F := BinaryFourCubicFibreTransportGauge.pointEquiv pi s fixed moving' hpi (by simp)
  have hsF : F.symm.permCongrHom
      (MulAction.toPermHom (preE7NonPairAction 16 U) (Fin 16) s) =
        BinaryFourCubicNormalizerPointShapes.rotation := by
    apply Equiv.ext
    intro p
    apply F.injective
    change F (F.symm (s • F p)) = F (BinaryFourCubicNormalizerPointShapes.rotation p)
    rw [F.apply_symm_apply]
    exact (BinaryFourCubicFibreTransportGauge.pointEquiv_rotation
      pi s fixed moving' hpi (by simp) hs3 hfixedAction p).symm
  have hzF : F.symm.permCongrHom
      (MulAction.toPermHom (preE7NonPairAction 16 U) (Fin 16) z) =
        BinaryFourCubicNormalizerPointShapes.translation ![1,0] := by
    apply Equiv.ext
    intro p
    apply F.injective
    change F (F.symm ((z : preE7NonPairAction 16 U) • F p)) =
      F (BinaryFourCubicNormalizerPointShapes.translation ![1,0] p)
    rw [F.apply_symm_apply]
    exact (BinaryFourCubicFibreTransportGauge.pointEquiv_translation
      pi s fixed moving' hpi (by simp) z ![1,0]
        (fun y => (hcommute y).symm) hzfixed hb p).symm
  exact BinaryFourCubicNormalizerShapeHead.translation_head_le_six F.symm S s z hgen
    (Subgroup.centralizer_le_normalizer _ hz) ![1,0] (by decide +kernel)
    hsF hzF x f hf rho hL hdim hrho B

namespace DegreeFourA4OriginalPointChart

theorem centralizingTranslation_physical_head
    (C : DegreeFourA4OriginalPointChart block)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (S : Sylow 3 (preE7NonPairAction 16 U)) (s : preE7NonPairAction 16 U)
    (d : block.Points ≃ Fin 4)
    (hgen : (S : Subgroup (preE7NonPairAction 16 U)) = Subgroup.zpowers s)
    (hs3 : s^3 = 1) (hsq : QuotientGroup.mk' (E block P) s ≠ 1)
    (hd : ∀ i : block.Points, d (s • i) = blockCycle (d i))
    (z : E block P) (hzne : (z : preE7NonPairAction 16 U) ≠ 1)
    (hz : (z : preE7NonPairAction 16 U) ∈
      Subgroup.centralizer (S : Set (preE7NonPairAction 16 U)))
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (f : MulAction.stabilizer (preE7NonPairAction 16 U) x →* L)
    (hf : Function.Surjective f) (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction 16 U) x).subtype
        (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (preE7NonPairAction 16 U) (ZMod 2))) ≤ 6 :=
  physical_head block P hr S s d hgen hs3 hsq hd
    (originalLocalMap_injective_at block P C hr hD (d.symm 0))
    z hzne hz x f hf rho hL hdim hrho B

end DegreeFourA4OriginalPointChart

namespace DegreeFourS4OriginalPointChart

theorem centralizingTranslation_physical_head
    (C : DegreeFourS4OriginalPointChart block)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (S : Sylow 3 (preE7NonPairAction 16 U)) (s : preE7NonPairAction 16 U)
    (d : block.Points ≃ Fin 4)
    (hgen : (S : Subgroup (preE7NonPairAction 16 U)) = Subgroup.zpowers s)
    (hs3 : s^3 = 1) (hsq : QuotientGroup.mk' (E block P) s ≠ 1)
    (hd : ∀ i : block.Points, d (s • i) = blockCycle (d i))
    (z : E block P) (hzne : (z : preE7NonPairAction 16 U) ≠ 1)
    (hz : (z : preE7NonPairAction 16 U) ∈
      Subgroup.centralizer (S : Set (preE7NonPairAction 16 U)))
    {L V : Type} [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (f : MulAction.stabilizer (preE7NonPairAction 16 U) x →* L)
    (hf : Function.Surjective f) (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (preE7NonPairAction 16 U) x).subtype
        (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (preE7NonPairAction 16 U) (ZMod 2))) ≤ 6 :=
  physical_head block P hr S s d hgen hs3 hsq hd
    (originalLocalMap_injective_at block P C hr hD (d.symm 0))
    z hzne hz x f hf rho hL hdim hrho B

end DegreeFourS4OriginalPointChart

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
