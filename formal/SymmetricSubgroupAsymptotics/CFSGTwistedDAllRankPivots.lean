import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeFixedGroup
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity

/-! Explicit fixed-field SL pivots in the literal relative-root group
in every rank at least three, including the genuine rank-three base. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPivots
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGTwistedA2FixedField CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDAllRankChainLift CFSGTwistedDAllRankChainAction

def negativeCoordinates (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v) :
    Fin (n + 2) → fixedField q := fun i =>
  ⟨v (Sum.inr i.castSucc), CFSGTwistedDFixedVectorCoordinates.negative_fixed
    (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v hv i.castSucc (Fin.castSucc_ne_last i)⟩

theorem preserves_fixed (n : ℕ) (q : CFSG.PrimePower)
    (u : relativeRootGroup (n + 1) q) (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v) :
    vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2)
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) =
        (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v :=
  CFSGTwistedDRelativeFixedGroup.relative_preserves_fixed_vectors (n + 1) q u v hv

theorem exists_negative_pivot (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hn : ∃ i : Fin (n + 2), v (Sum.inr i.castSucc) ≠ 0) :
    ∃ u : relativeRootGroup (n + 1) q,
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (Sum.inr (pen (n + 1))) = 1 ∧
      vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2)
        ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) =
          (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v := by
  let w := negativeCoordinates n q v hv
  have hw : w ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := hn
    have h := congrArg (fun z : fixedField q => (z : q.Extension 2)) (congrFun he i)
    exact hi h
  have hp : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
    intro he
    have h := congrArg Fin.val he
    change n + 1 = 0 at h
    omega
  obtain ⟨A, hA⟩ := CFSGTypeAVectorTransitivity.exists_normalize
    (Fin.last (n + 1)) 0 hp w hw
  change A.val *ᵥ w = Pi.single (Fin.last (n + 1)) 1 at hA
  let u : relativeRootGroup (n + 1) q :=
    ⟨chainLift (n + 1) q (A⁻¹).transpose, chainLift_mem (n + 1) q (A⁻¹).transpose⟩
  refine ⟨u, ?_, preserves_fixed n q u v hv⟩
  change ((chainLift (n + 1) q (A⁻¹).transpose : Mat (q.Extension 2) (n + 3)) *ᵥ v)
    (Sum.inr (Fin.last (n + 1)).castSucc) = 1
  rw [inverseTranspose_negative_castSucc]
  change ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
    (fun i => ((w i : fixedField q) : q.Extension 2))) (Fin.last (n + 1)) = 1
  have he := RingHom.map_mulVec (fixedField q).subtype A.val w (Fin.last (n + 1))
  change ((A.val *ᵥ w) (Fin.last (n + 1)) : q.Extension 2) = _ at he
  change (A.val.map (fixedField q).subtype *ᵥ ((fixedField q).subtype ∘ w))
    (Fin.last (n + 1)) = 1
  rw [← he, hA, Pi.single_eq_same]
  rfl


theorem exists_positive_pivot (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hn : ∃ i : Fin (n + 2), v (Sum.inl i.castSucc) ≠ 0)
    (hz : v ∘ Sum.inr = 0) (hl : v (Sum.inl (last (n + 1))) = 0) :
    ∃ u : relativeRootGroup (n + 1) q,
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (Sum.inl (pen (n + 1))) = 1 ∧
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) ∘ Sum.inr = 0 ∧
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
        (Sum.inl (last (n + 1))) = 0 ∧
      vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2)
        ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) =
          (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v := by
  let w : Fin (n + 2) → fixedField q := fun i =>
    ⟨v (Sum.inl i.castSucc),
      CFSGTwistedDFixedVectorCoordinates.positive_fixed (q.Extension 2) (n + 1)
        (definingFieldAutomorphism q 2) v hv i.castSucc (Fin.castSucc_ne_last i)⟩
  have hw : w ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := hn
    exact hi (congrArg (fun z : fixedField q => (z : q.Extension 2)) (congrFun he i))
  have hp : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
    intro he
    have h := congrArg Fin.val he
    change n + 1 = 0 at h
    omega
  obtain ⟨A, hA⟩ := CFSGTypeAVectorTransitivity.exists_normalize
    (Fin.last (n + 1)) 0 hp w hw
  change A.val *ᵥ w = Pi.single (Fin.last (n + 1)) 1 at hA
  let u : relativeRootGroup (n + 1) q := ⟨chainLift (n + 1) q A, chainLift_mem (n + 1) q A⟩
  refine ⟨u, ?_, negative_zero (n + 1) q A v hz, ?_,
    preserves_fixed n q u v hv⟩
  · change ((chainLift (n + 1) q A : Mat (q.Extension 2) (n + 3)) *ᵥ v)
      (Sum.inl (Fin.last (n + 1)).castSucc) = 1
    rw [positive_castSucc]
    change ((Matrix.SpecialLinearGroup.map (fixedField q).subtype A).val *ᵥ
      (fun i => ((w i : fixedField q) : q.Extension 2))) (Fin.last (n + 1)) = 1
    have he := RingHom.map_mulVec (fixedField q).subtype A.val w (Fin.last (n + 1))
    change ((A.val *ᵥ w) (Fin.last (n + 1)) : q.Extension 2) = _ at he
    change (A.val.map (fixedField q).subtype *ᵥ ((fixedField q).subtype ∘ w))
      (Fin.last (n + 1)) = 1
    rw [← he, hA, Pi.single_eq_same]
    rfl
  · change ((chainLift (n + 1) q A : Mat (q.Extension 2) (n + 3)) *ᵥ v)
      (Sum.inl (Fin.last (n + 2))) = 0
    rw [positive_last]
    exact hl


end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPivots
