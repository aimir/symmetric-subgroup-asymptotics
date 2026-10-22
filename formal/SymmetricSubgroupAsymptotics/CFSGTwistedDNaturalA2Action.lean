import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
import SymmetricSubgroupAsymptotics.CFSGTwistedDA2MatrixWitness
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDImageRealization

/-! The original fixed/derived words act on the SAME integral natural-D
image as literal A2 matrix words. No simplicity of the ambient untwisted
group, or faithfulness of its Lie realization, is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationSLDouble
open CFSGTwistedDA2MatrixWitness CFSGSerreSquareZeroMatrix
variable (K : Type) [Field K] (s : ℕ)

def coordinate (i : Fin 3) : Fin (s + 4) := ⟨i.val, by have := i.isLt; omega⟩

theorem coordinate_ne {i j : Fin 3} (hij : i ≠ j) : coordinate s i ≠ coordinate s j := by
  intro h
  have hv : i.val = j.val := congrArg (fun k : Fin (s + 4) => k.val) h
  exact hij (Fin.ext hv)

def naturalRoot (neg : Bool) (i : Fin 2) (a : K) : elementaryRootGroup K (s + 4) :=
  ⟨rootTransvection K (s + 4) neg (node s i) a,
    rootTransvection_mem K (s + 4) neg (node s i) a⟩

def nextCoordinate (i : Fin 2) : Fin (s + 4) :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

theorem node_ne_next (i : Fin 2) : node s i ≠ nextCoordinate s i := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = i.val + 1 at hh
  omega

theorem naturalRoot_positive (i : Fin 2) (a : K) :
    naturalRoot K s false i a =
      chain K (s + 4) (node s i) (nextCoordinate s i) (node_ne_next s i) a := by
  have hi : (node s i).val + 1 < s + 4 := by have := i.isLt; dsimp only [node]; omega
  apply Subtype.ext
  apply Units.ext
  change 1 + a • positive K (s + 4) (node s i) =
    ((doubleHom K (s + 4) (CFSGTypeAElementaryMatrices.elementary (node_ne_next s i) a)) : Mat K (s + 4))
  rw [doubleHom_elementary_val, positive, dif_pos hi] <;> rfl

theorem naturalRoot_negative (i : Fin 2) (a : K) :
    naturalRoot K s true i a =
      chain K (s + 4) (nextCoordinate s i) (node s i) (Ne.symm (node_ne_next s i)) a := by
  have hi : (node s i).val + 1 < s + 4 := by have := i.isLt; dsimp only [node]; omega
  apply Subtype.ext
  apply Units.ext
  change 1 + a • negative K (s + 4) (node s i) =
    ((doubleHom K (s + 4) (CFSGTypeAElementaryMatrices.elementary (Ne.symm (node_ne_next s i)) a)) :
      Mat K (s + 4))
  rw [doubleHom_elementary_val, negative, positive, dif_pos hi]
  simp only [Matrix.transpose_sub, Matrix.transpose_single, chainMatrix] <;> rfl

def fixedImageAction (q : CFSG.PrimePower) :=
  (orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega)).comp (toModel s q)

def derivedImageAction (q : CFSG.PrimePower) :=
  (orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega)).comp (derivedToOriginal s q)

def naturalAction (q : CFSG.PrimePower) : elementaryRootGroup (q.Extension 2) (s + 4) →*
    ((orthogonalBaseChange (q.Extension 2) (s + 4) (by omega)).range ≃ₗ[q.Extension 2]
      (orthogonalBaseChange (q.Extension 2) (s + 4) (by omega)).range) :=
  elementaryImageAction (q.Extension 2) (s + 4) (by omega)

theorem fixedRoot_image (q : CFSG.PrimePower) (neg : Bool) (i : Fin 2)
    (t : q.Extension 2) (ht : CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 t = t) :
    fixedImageAction s q (root s q neg i t ht) = naturalAction s q (naturalRoot (q.Extension 2) s neg i t) := by
  change orthogonalImageRepresentation (q.Extension 2) (s + 4) (by omega)
    (CFSGSerreModelRootGeneration.modelRoot (CartanMatrix.D (s + 4)) (q.Extension 2) neg (node s i) t) = _
  exact source_root_action_eq_elementary (realizationData (s + 4) (by omega)) (q.Extension 2)
    (rootTransvection (q.Extension 2) (s + 4))
    (rootTransvection_val_data (q.Extension 2) (s + 4) (by omega))
    (rootTransvection_inv_val_data (q.Extension 2) (s + 4) (by omega)) neg (node s i) t

theorem positiveWord_image (q : CFSG.PrimePower) :
    derivedImageAction s q (positiveWord s q) = naturalAction s q
      (chain (q.Extension 2) (s + 4) (coordinate s 0) (coordinate s 2)
        (coordinate_ne s (by decide)) 1) := by
  change fixedImageAction s q ⁅root s q false 0 1 (one_fixed q), root s q false 1 1 (one_fixed q)⁆ = _
  rw [map_commutatorElement, fixedRoot_image, fixedRoot_image,
    naturalRoot_positive, naturalRoot_positive, ← map_commutatorElement]
  change naturalAction s q ⁅chain (q.Extension 2) (s + 4) (coordinate s 0) (coordinate s 1)
    (coordinate_ne s (by decide)) 1,
      chain (q.Extension 2) (s + 4) (coordinate s 1) (coordinate s 2)
        (coordinate_ne s (by decide)) 1⁆ = _
  simpa only [mul_one] using congrArg (naturalAction s q)
    (chain_commutator (q.Extension 2) (s + 4) (coordinate s 0) (coordinate s 1) (coordinate s 2)
      (coordinate_ne s (by decide)) (coordinate_ne s (by decide)) (coordinate_ne s (by decide)) 1 1)

theorem negativeWord_image (q : CFSG.PrimePower) :
    derivedImageAction s q (negativeWord s q) = naturalAction s q
      (chain (q.Extension 2) (s + 4) (coordinate s 2) (coordinate s 0)
        (coordinate_ne s (by decide)) 1) := by
  change fixedImageAction s q ⁅root s q true 1 1 (one_fixed q), root s q true 0 1 (one_fixed q)⁆ = _
  rw [map_commutatorElement, fixedRoot_image, fixedRoot_image,
    naturalRoot_negative, naturalRoot_negative, ← map_commutatorElement]
  change naturalAction s q ⁅chain (q.Extension 2) (s + 4) (coordinate s 2) (coordinate s 1)
    (coordinate_ne s (by decide)) 1,
      chain (q.Extension 2) (s + 4) (coordinate s 1) (coordinate s 0)
        (coordinate_ne s (by decide)) 1⁆ = _
  simpa only [mul_one] using congrArg (naturalAction s q)
    (chain_commutator (q.Extension 2) (s + 4) (coordinate s 2) (coordinate s 1) (coordinate s 0)
      (coordinate_ne s (by decide)) (coordinate_ne s (by decide)) (coordinate_ne s (by decide)) 1 1)

theorem weylWord_image (q : CFSG.PrimePower) :
    derivedImageAction s q (weylWord s q) = naturalAction s q
      (CFSGTwistedDA2MatrixWitness.naturalWeyl (q.Extension 2) (s + 4)
        (coordinate s 0) (coordinate s 2) (coordinate_ne s (by decide))) := by
  rw [CFSGTwistedDA2MatrixWitness.naturalWeyl_word]
  simp only [weylWord, map_mul, map_inv, positiveWord_image, negativeWord_image]

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedA2
