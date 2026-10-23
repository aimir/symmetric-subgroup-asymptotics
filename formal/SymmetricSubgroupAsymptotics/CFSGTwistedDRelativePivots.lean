import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeChainLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeFixedGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedDNegativePivot
import SymmetricSubgroupAsymptotics.CFSGTwistedDPositivePivot

/-! The explicit positive and negative pivot words belong to the literal
relative-root subgroup. Their fixed-vector action is proved from the
actual natural involution, independently of the larger Derived
preimage orbit theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePivots
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedA2FixedField CFSGTwistedDFixedChainLift
open CFSGTwistedDFixedChainAction CFSGTwistedDFixedChainPositiveAction
open CFSGTwistedDRelativeChainLift CFSGTwistedDNegativePivot

theorem preserves_fixed (s : ℕ) (q : CFSG.PrimePower)
    (u : relativePreimage s q) (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v) :
    vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) =
        (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v :=
  CFSGTwistedDRelativeFixedGroup.relative_preserves_fixed_vectors (s + 2) q
    ⟨u.val.val, u.property⟩ v hv

theorem exists_negative_pivot (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hn : ∃ i : Fin (s + 3), v (Sum.inr i.castSucc) ≠ 0) :
    ∃ u : relativePreimage s q,
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
  let u : relativePreimage s q :=
    ⟨fixedChainLift s q (A⁻¹).transpose, CFSGTwistedDRelativeChainLift.fixedChainLift_mem s q (A⁻¹).transpose⟩
  refine ⟨u, ?_, preserves_fixed s q u v hv⟩
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


theorem exists_positive_pivot (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hn : ∃ i : Fin (s + 3), v (Sum.inl i.castSucc) ≠ 0)
    (hz : v ∘ Sum.inr = 0) (hl : v (Sum.inl (last (s + 2))) = 0) :
    ∃ u : relativePreimage s q,
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
  let u : relativePreimage s q := ⟨fixedChainLift s q A, CFSGTwistedDRelativeChainLift.fixedChainLift_mem s q A⟩
  refine ⟨u, ?_, negative_zero s q A v hz, ?_,
    preserves_fixed s q u v hv⟩
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


end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePivots
