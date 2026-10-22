import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorAction

/-! Actual fixed-field SL words normalize any nonzero untouched negative
coordinate vector to the preceding pivot. The witness remains above the
same original Derived action image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNegativePivot
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedA2FixedField CFSGTwistedDFixedChainLift
open CFSGTwistedDFixedChainAction CFSGTwistedDDerivedPairedRoots

theorem castSucc_ne_last (s : ℕ) (i : Fin (s + 3)) :
    i.castSucc ≠ last (s + 2) := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = s + 3 at hh
  have := i.isLt
  omega

def negativeCoordinates (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v) :
    Fin (s + 3) → fixedField q := fun i =>
  ⟨v (Sum.inr i.castSucc),
    CFSGTwistedDFixedVectorCoordinates.negative_fixed (q.Extension 2) (s + 2)
      (definingFieldAutomorphism q 2) v hv i.castSucc (castSucc_ne_last s i)⟩

theorem exists_negative_pivot (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hn : ∃ i : Fin (s + 3), v (Sum.inr i.castSucc) ≠ 0) :
    ∃ u : naturalDerivedPreimage s q,
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inr (pen (s + 2))) = 1 ∧
      vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
        ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) =
          (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v := by
  let w := negativeCoordinates s q v hv
  have hw : w ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := hn
    have h := congrArg (fun z : fixedField q => (z : q.Extension 2)) (congrFun he i)
    exact hi h
  have hp : (Fin.last (s + 2) : Fin (s + 3)) ≠ 0 := by
    intro he
    have h := congrArg Fin.val he
    change s + 2 = 0 at h
    omega
  obtain ⟨A, hA⟩ := CFSGTypeAVectorTransitivity.exists_normalize
    (Fin.last (s + 2)) 0 hp w hw
  change A.val *ᵥ w = Pi.single (Fin.last (s + 2)) 1 at hA
  let u : naturalDerivedPreimage s q :=
    ⟨fixedChainLift s q (A⁻¹).transpose, fixedChainLift_mem s q (A⁻¹).transpose⟩
  refine ⟨u, ?_, CFSGTwistedDFixedVectorAction.derived_preserves_fixed_vectors s q u v hv⟩
  change (((fixedChainLift s q (A⁻¹).transpose).val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
    (Sum.inr (Fin.last (s + 2)).castSucc) = 1
  rw [inverseTranspose_negative_castSucc]
  change ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
    (fun i => ((w i : fixedField q) : q.Extension 2))) (Fin.last (s + 2)) = 1
  have he := RingHom.map_mulVec (fixedField q).subtype A.val w (Fin.last (s + 2))
  change ((A.val *ᵥ w) (Fin.last (s + 2)) : q.Extension 2) = _ at he
  change (A.val.map (fixedField q).subtype *ᵥ ((fixedField q).subtype ∘ w))
    (Fin.last (s + 2)) = 1
  rw [← he, hA, Pi.single_eq_same]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDNegativePivot
