import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinaryImageTarget
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalCanonicalCoreAction
import SymmetricSubgroupAsymptotics.BinaryFourOriginalScalarFrameCompatibility

/-! The middle-supported source is constructed for each actual original
retained binary-socle intersection. Every local chart, scalar transport,
Klein-triviality fact and source case split is discharged internally. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open BinaryFourBlockAugmentation

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourOriginalBinaryMiddleSource_localFact1 : Fact P.p.Prime := ⟨P.p_prime⟩

local instance originalBinaryMiddleSource_coordinateModule :
    _root_.Module (ZMod (elementaryChart block P).p) (Fin 8 → ZMod P.p) := by
  change _root_.Module (ZMod P.p) (Fin 8 → ZMod P.p)
  infer_instance

abbrev degreeFourOriginalBinaryTargetRepresentation
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (DegreeFourFullBinaryTargetSection block P N).toRepresentation.comp
    (degreeFourFullBinarySocleTopMap block P N)

namespace DegreeFourS4OriginalPointChart

variable (C : DegreeFourS4OriginalPointChart block)

set_option maxHeartbeats 1000000 in
theorem originalBinaryMiddleSource
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Nonempty (OriginalMiddleSourceAt (degreeFour_profilePrime_eq_two block P hr)
      ((canonicalMap (block := block) (P := P) (C := C) hr hD)) (degreeFourOriginalBinaryTargetRepresentation block P N)) := by
  let hp := degreeFour_profilePrime_eq_two block P hr
  let gamma := (canonicalMap (block := block) (P := P) (C := C) hr hD)
  let rho : Representation (ZMod P.p) (preE7NonPairAction w U) (Fin 8 → ZMod P.p) :=
    canonicalFullAt hp gamma
  let i0 : (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap
      ((BinaryFourOriginalScalarCharts.s4Frame hp
        (groupEquiv (block := block) (P := P) (C := C) hr hD)).comp
          (QuotientGroup.mk' (E block P))) :=
    (binarySectionCoordinates (block := block) (P := P) (C := C) hr hD) N
  have heq :
      (BinaryFourOriginalScalarCharts.s4Frame hp ((groupEquiv (block := block) (P := P) (C := C) hr hD))).comp
        (QuotientGroup.mk' (E block P)) = rho :=
    s4_original_frame_comp hp ((groupEquiv (block := block) (P := P) (C := C) hr hD)) (QuotientGroup.mk' (E block P))
  let i : (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap rho := {
    toLinearMap := i0.toLinearMap
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      change i0 ((DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation g x) =
        rho g (i0 x)
      have h := Representation.IntertwiningMap.isIntertwining _ _ i0 g x
      have heval := congrArg
        (fun r : Representation (ZMod P.p) (preE7NonPairAction w U)
          (Fin 8 → ZMod P.p) => r g (i0 x)) heq
      exact h.trans heval }
  have hi : Function.Injective i := by
    intro x y h
    change i0 x = i0 y at h
    exact (binarySectionCoordinates_injective
      (block := block) (P := P) (C := C) hr hD N) h
  let L := i.range
  let tau := degreeFourOriginalBinaryTargetRepresentation block P N
  let f := originalBinaryImageTargetMap block P N rho i hi
  have hf : Function.Surjective f := originalBinaryImageTargetMap_surjective block P N rho i hi
  apply originalMiddleSource_exists_at hp gamma ((canonicalMap_even_lifts (block := block) (P := P) (C := C) hr hD)) L tau f hf
  intro g hg v
  exact (binaryTarget_fixed_by_canonicalKlein (block := block) (P := P) (C := C) hr hD) N g hg v

end DegreeFourS4OriginalPointChart

namespace DegreeFourA4OriginalPointChart

variable (C : DegreeFourA4OriginalPointChart block)

set_option maxHeartbeats 1000000 in
theorem originalBinaryMiddleSource
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Nonempty (OriginalMiddleSourceAt (degreeFour_profilePrime_eq_two block P hr)
      ((canonicalMap (block := block) (P := P) (C := C) hr hD)) (degreeFourOriginalBinaryTargetRepresentation block P N)) := by
  let hp := degreeFour_profilePrime_eq_two block P hr
  let gamma := (canonicalMap (block := block) (P := P) (C := C) hr hD)
  let rho : Representation (ZMod P.p) (preE7NonPairAction w U) (Fin 8 → ZMod P.p) :=
    canonicalFullAt hp gamma
  let i0 : (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap
      ((BinaryFourOriginalScalarCharts.a4Frame hp
        (groupEquiv (block := block) (P := P) (C := C) hr hD)).comp
          (QuotientGroup.mk' (E block P))) :=
    (binarySectionCoordinates (block := block) (P := P) (C := C) hr hD) N
  have heq :
      (BinaryFourOriginalScalarCharts.a4Frame hp ((groupEquiv (block := block) (P := P) (C := C) hr hD))).comp
        (QuotientGroup.mk' (E block P)) = rho :=
    a4_original_frame_comp hp ((groupEquiv (block := block) (P := P) (C := C) hr hD)) (QuotientGroup.mk' (E block P))
  let i : (DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation.IntertwiningMap rho := {
    toLinearMap := i0.toLinearMap
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      change i0 ((DegreeFourFullBinarySourceSectionInflated block P N).toRepresentation g x) =
        rho g (i0 x)
      have h := Representation.IntertwiningMap.isIntertwining _ _ i0 g x
      have heval := congrArg
        (fun r : Representation (ZMod P.p) (preE7NonPairAction w U)
          (Fin 8 → ZMod P.p) => r g (i0 x)) heq
      exact h.trans heval }
  have hi : Function.Injective i := by
    intro x y h
    change i0 x = i0 y at h
    exact (binarySectionCoordinates_injective
      (block := block) (P := P) (C := C) hr hD N) h
  let L := i.range
  let tau := degreeFourOriginalBinaryTargetRepresentation block P N
  let f := originalBinaryImageTargetMap block P N rho i hi
  have hf : Function.Surjective f := originalBinaryImageTargetMap_surjective block P N rho i hi
  apply originalMiddleSource_exists_at hp gamma ((canonicalMap_even_lifts (block := block) (P := P) (C := C) hr hD)) L tau f hf
  intro g hg v
  exact (binaryTarget_fixed_by_canonicalKlein (block := block) (P := P) (C := C) hr hD) N g hg v

end DegreeFourA4OriginalPointChart

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
