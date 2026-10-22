import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainPositiveAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorAction

/-! Actual fixed-chain words normalize a nonzero positive half while
retaining a zero negative half and zero final positive coordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPositivePivot
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedA2FixedField CFSGTwistedDFixedChainLift
open CFSGTwistedDFixedChainPositiveAction CFSGTwistedDDerivedPairedRoots

theorem exists_positive_pivot (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hn : ∃ i : Fin (s + 3), v (Sum.inl i.castSucc) ≠ 0)
    (hz : v ∘ Sum.inr = 0) (hl : v (Sum.inl (last (s + 2))) = 0) :
    ∃ u : naturalDerivedPreimage s q,
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inl (pen (s + 2))) = 1 ∧
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) ∘ Sum.inr = 0 ∧
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inl (last (s + 2))) = 0 ∧
      vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
        ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) =
          (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v := by
  let w : Fin (s + 3) → fixedField q := fun i =>
    ⟨v (Sum.inl i.castSucc),
      CFSGTwistedDFixedVectorCoordinates.positive_fixed (q.Extension 2) (s + 2)
        (definingFieldAutomorphism q 2) v hv i.castSucc (Fin.castSucc_ne_last i)⟩
  have hw : w ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := hn
    exact hi (congrArg (fun z : fixedField q => (z : q.Extension 2)) (congrFun he i))
  have hp : (Fin.last (s + 2) : Fin (s + 3)) ≠ 0 := by
    intro he
    have h := congrArg Fin.val he
    change s + 2 = 0 at h
    omega
  obtain ⟨A, hA⟩ := CFSGTypeAVectorTransitivity.exists_normalize
    (Fin.last (s + 2)) 0 hp w hw
  change A.val *ᵥ w = Pi.single (Fin.last (s + 2)) 1 at hA
  let u : naturalDerivedPreimage s q := ⟨fixedChainLift s q A, fixedChainLift_mem s q A⟩
  refine ⟨u, ?_, negative_zero s q A v hz, ?_,
    CFSGTwistedDFixedVectorAction.derived_preserves_fixed_vectors s q u v hv⟩
  · change (((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
      (Sum.inl (Fin.last (s + 2)).castSucc) = 1
    rw [positive_castSucc]
    change ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
      (fun i => ((w i : fixedField q) : q.Extension 2))) (Fin.last (s + 2)) = 1
    have he := RingHom.map_mulVec (fixedField q).subtype A.val w (Fin.last (s + 2))
    change ((A.val *ᵥ w) (Fin.last (s + 2)) : q.Extension 2) = _ at he
    change (A.val.map (fixedField q).subtype *ᵥ ((fixedField q).subtype ∘ w))
      (Fin.last (s + 2)) = 1
    rw [← he, hA, Pi.single_eq_same]
    rfl
  · change (((fixedChainLift s q A).val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
      (Sum.inl (Fin.last (s + 3))) = 0
    rw [positive_last]
    exact hl

end SymmetricSubgroupAsymptotics.CFSGTwistedDPositivePivot
