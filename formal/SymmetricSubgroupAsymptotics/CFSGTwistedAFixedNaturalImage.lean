import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalFieldTwist

/-!
# A genuine equation on the natural image of the ORIGINAL fixed group

Every literal fixed element commutes, on its actual tensor image, with
the signed diagram--Frobenius matrix map. This is only an equation on
that original image. Reconstructing natural matrices and resolving the
projectively fixed scalar obstruction are separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
open CFSG.Models.Chevalley

section Field
variable (K : Type) [Field K] (σ : K ≃+* K)

local instance cfsgTwistedANaturalSigmaInvPair :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ
local instance cfsgTwistedANaturalSigmaSymmInvPair :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.of_ringEquiv_symm σ

theorem original_diagram_field_intertwines (r : ℕ)
    (g : Ambient (CartanMatrix.A r) K) (x : Space (CartanMatrix.A r) K) :
    CFSGSerreFieldDiagram.ambientAutomorphism (CartanMatrix.A r) K Fin.revPerm
      (CFSGSerreDiagram.typeA_reverse_preserves r) σ g
      (CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) K Fin.revPerm
        (CFSGSerreDiagram.typeA_reverse_preserves r)
        (CFSGSerreField.tensorEquiv (CartanMatrix.A r) K σ x)) =
      CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) K Fin.revPerm
        (CFSGSerreDiagram.typeA_reverse_preserves r)
        (CFSGSerreField.tensorEquiv (CartanMatrix.A r) K σ (g x)) := by
  change CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) K Fin.revPerm
      (CFSGSerreDiagram.typeA_reverse_preserves r)
      (CFSGSerreField.ambientAutomorphism (CartanMatrix.A r) K σ g
        ((CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) K Fin.revPerm
          (CFSGSerreDiagram.typeA_reverse_preserves r)).symm
          (CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) K Fin.revPerm
            (CFSGSerreDiagram.typeA_reverse_preserves r)
            (CFSGSerreField.semilinearEquiv (CartanMatrix.A r) K σ x)))) = _
  rw [LinearEquiv.symm_apply_apply, CFSGSerreField.ambientAutomorphism_apply,
    LinearEquiv.symm_apply_apply] <;> rfl

end Field

def originalTwistSpace (r : ℕ) (q : CFSG.PrimePower)
    (x : Space (CartanMatrix.A r) (q.Extension 2)) : Space (CartanMatrix.A r) (q.Extension 2) :=
  CFSGSerreDiagram.spaceEquiv (CartanMatrix.A r) (q.Extension 2) Fin.revPerm
    (CFSGSerreDiagram.typeA_reverse_preserves r)
    (CFSGSerreField.tensorEquiv (CartanMatrix.A r) (q.Extension 2)
      (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) x)

def naturalTwistMatrix (r : ℕ) (q : CFSG.PrimePower) (X : Mat (q.Extension 2) r) :
    Mat (q.Extension 2) r :=
  matrixDiagram (q.Extension 2) r
    ((CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2).toRingHom.mapMatrix X)

theorem naturalBaseChange_twistSpace (r : ℕ) (q : CFSG.PrimePower)
    (x : Space (CartanMatrix.A r) (q.Extension 2)) :
    CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2)
      (originalTwistSpace r q x) =
      naturalTwistMatrix r q
        (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) x) :=
  naturalBaseChange_ordinaryTwistSpace r q x

theorem fixed_original_twist_commutes (r : ℕ) (q : CFSG.PrimePower)
    (g : fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode
      (fun _ => q.order)) (x : Space (CartanMatrix.A r) (q.Extension 2)) :
    originalTwistSpace r q (g.val x) = g.val (originalTwistSpace r q x) := by
  have hfix : CFSGSerreOrdinaryTwists.typeAAmbientAction r q g.val = g.val := by
    exact ((CFSGSerreOrdinaryTwists.typeA_mem_twistGraph_iff r q
      (g.val, g.val)).mp g.property.2).2.symm
  have hh := original_diagram_field_intertwines (q.Extension 2)
    (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2) r g.val x
  change CFSGSerreOrdinaryTwists.typeAAmbientAction r q g.val
    (originalTwistSpace r q x) = originalTwistSpace r q (g.val x) at hh
  rw [hfix] at hh
  exact hh.symm

theorem fixed_natural_image_equation (r : ℕ) (q : CFSG.PrimePower)
    (g : fixedSubgroup (CartanMatrix.A r) (q.Extension 2) CFSG.Models.reverseNode
      (fun _ => q.order)) (x : Space (CartanMatrix.A r) (q.Extension 2)) :
    naturalTwistMatrix r q
      (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) (g.val x)) =
      CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2)
        (g.val (originalTwistSpace r q x)) := by
  rw [← naturalBaseChange_twistSpace, fixed_original_twist_commutes]

theorem derived_natural_image_equation (r : ℕ) (q : CFSG.PrimePower)
    (g : commutator (fixedSubgroup (CartanMatrix.A r) (q.Extension 2)
      CFSG.Models.reverseNode (fun _ => q.order)))
    (x : Space (CartanMatrix.A r) (q.Extension 2)) :
    naturalTwistMatrix r q
      (CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2) (g.val.val x)) =
      CFSGSerreSquareZeroMatrix.baseChange (realizationData r) (q.Extension 2)
        (g.val.val (originalTwistSpace r q x)) :=
  fixed_natural_image_equation r q g.val x

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
