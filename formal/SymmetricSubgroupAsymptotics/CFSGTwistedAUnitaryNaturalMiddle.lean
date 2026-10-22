import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleArrays
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalForm
import SymmetricSubgroupAsymptotics.CFSGTwistedAUpperUnipotent

/-! Literal defining-fixed middle block embedding. Every map is built
from diag(1,A,1) on the existing natural elementary groups, and fixedness
is proved for the SAME signed reversal/Frobenius equation. No unitary
recognition, simplicity or derived membership is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent CFSGSerreOrdinaryTwists

theorem fixed_unit_signedForm (K : Type) [Field K] (s : ℕ) (f : K →+* K)
    (A : (Mat K s)ˣ) (hA : diagramFieldUnitHom K s f A = A) :
    (f.mapMatrix (A : Mat K s)).transpose * (signedReversalUnit K s : Mat K s) *
      (A : Mat K s) = (signedReversalUnit K s : Mat K s) := by
  have h := fixed_unit_isometric K s f A hA
  have he : ((-1 : K) ^ s) * ((-1 : K) ^ s) = 1 := by
    rw [← mul_pow]
    simp
  have hJ : (signedReversalUnit K s : Mat K s) =
      ((-1 : K) ^ s) • (↑((signedReversalUnit K s)⁻¹) : Mat K s) := by
    rw [signedReversalUnit_inv_parity, smul_smul, he, one_smul]
  calc
    _ = ((-1 : K) ^ s) • ((f.mapMatrix (A : Mat K s)).transpose *
        (↑((signedReversalUnit K s)⁻¹) : Mat K s) * (A : Mat K s)) := by
      rw [hJ]
      simp only [mul_smul_comm, smul_mul_assoc]
    _ = ((-1 : K) ^ s) • (↑((signedReversalUnit K s)⁻¹) : Mat K s) :=
      congrArg (fun M : Mat K s => ((-1 : K) ^ s) • M) h
    _ = _ := hJ.symm

def naturalMiddleUnitHom (K : Type) [Field K] (s : ℕ) :
    (Mat K s)ˣ →* (Mat K (s + 2))ˣ :=
  (Units.map (Matrix.reindexAlgEquiv K K (splitEquiv s)).toRingHom.toMonoidHom).comp
    middleUnitHom

theorem naturalMiddleUnitHom_val (K : Type) [Field K] (s : ℕ) (A : (Mat K s)ˣ) :
    (naturalMiddleUnitHom K s A : Mat K (s + 2)) =
      Matrix.reindex (splitEquiv s) (splitEquiv s) (middleArray (A : Mat K s)) := rfl

theorem naturalMiddleUnitHom_det (K : Type) [Field K] (s : ℕ)
    (A : NaturalElementary K s) :
    (naturalMiddleUnitHom K s A.val : Mat K (s + 2)).det = 1 := by
  rw [naturalMiddleUnitHom_val, Matrix.det_reindex_self, middleArray_det]
  exact naturalElementary_det K s A

def naturalMiddleHom (K : Type) [Field K] (s : ℕ) :
    NaturalElementary K s →* NaturalElementary K (s + 2) where
  toFun A := ⟨naturalMiddleUnitHom K s A.val,
    unit_mem_natural_of_det K (s + 2) _ (naturalMiddleUnitHom_det K s A)⟩
  map_one' := Subtype.ext (map_one (naturalMiddleUnitHom K s))
  map_mul' A B := Subtype.ext (map_mul (naturalMiddleUnitHom K s) A.val B.val)

theorem naturalMiddleHom_injective (K : Type) [Field K] (s : ℕ) :
    Function.Injective (naturalMiddleHom K s) := by
  intro A B he
  apply Subtype.ext
  apply middleUnitHom_injective
  have hu := congrArg (fun u : NaturalElementary K (s + 2) => u.val) he
  exact (Units.map_injective (Matrix.reindexAlgEquiv K K (splitEquiv s)).injective) hu

theorem naturalMiddleHom_fixed (q : CFSG.PrimePower) (s : ℕ)
    (A : naturalFixed s q) : naturalMiddleHom (q.Extension 2) s A.val ∈ naturalFixed (s + 2) q := by
  have hs := fixed_unit_signedForm (q.Extension 2) s
    (definingFieldAutomorphism q 2).toRingHom A.val.val A.property
  have hm : (((A.val.val : Mat (q.Extension 2) s).map (definingFieldAutomorphism q 2)).transpose *
      (-(signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s))) *
      (A.val.val : Mat (q.Extension 2) s) = -(signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s) := by
    simpa only [mul_neg, neg_mul] using congrArg Neg.neg hs
  have hb := middleArray_isometry (definingFieldAutomorphism q 2).toRingHom
    ((-1 : q.Extension 2) ^ s) (-(signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s))
    (A.val.val : Mat (q.Extension 2) s) hm
  have hf := reindex_isometry (splitEquiv s) (definingFieldAutomorphism q 2).toRingHom
    _ _ hb
  rw [blockForm_reindex] at hf
  change diagramFieldUnitHom (q.Extension 2) (s + 2)
    (definingFieldAutomorphism q 2).toRingHom (naturalMiddleUnitHom (q.Extension 2) s A.val.val) = _
  apply unit_fixed_of_signedForm (q.Extension 2) (s + 2)
    (definingFieldAutomorphism q 2).toRingHom
  simpa only [naturalMiddleUnitHom_val] using hf

def naturalFixedMiddleHom (q : CFSG.PrimePower) (s : ℕ) : naturalFixed s q →* naturalFixed (s + 2) q where
  toFun A := ⟨naturalMiddleHom (q.Extension 2) s A.val, naturalMiddleHom_fixed q s A⟩
  map_one' := Subtype.ext (map_one (naturalMiddleHom (q.Extension 2) s))
  map_mul' A B := Subtype.ext (map_mul (naturalMiddleHom (q.Extension 2) s) A.val B.val)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
