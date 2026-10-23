import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import Mathlib.SetTheory.Cardinal.Finite

/-! A literal defining-fixed vector is determined by its two untouched
fixed-field coordinate strings and one extension-field coordinate.
This counts the actual carrier, without a nonsplit-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGTwistedDFixedVectorCoordinates
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists

def fixedVectors (n : ℕ) (q : CFSG.PrimePower) :=
  {v : Index (n + 2) → q.Extension 2 //
    vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) v = v}

def coordinateEncoding (n : ℕ) (q : CFSG.PrimePower) (v : fixedVectors n q) :
    (Fin (n + 1) → fixedField q) ×
      ((Fin (n + 1) → fixedField q) × q.Extension 2) :=
  (fun i => ⟨v.val (Sum.inl i.castSucc),
      positive_fixed (q.Extension 2) n _ v.val v.property i.castSucc
        (Fin.castSucc_ne_last i)⟩,
   (fun i => ⟨v.val (Sum.inr i.castSucc),
      negative_fixed (q.Extension 2) n _ v.val v.property i.castSucc
        (Fin.castSucc_ne_last i)⟩,
    v.val (Sum.inl (last n))))

theorem coordinateEncoding_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (coordinateEncoding n q) := by
  intro v w h
  have hp := congrArg Prod.fst h
  have hn := congrArg (fun z => z.2.1) h
  have hl := congrArg (fun z => z.2.2) h
  apply Subtype.ext
  funext x
  cases x with
  | inl i =>
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact congrArg (fun a : fixedField q => (a : q.Extension 2)) (congrFun hp j)
    · exact hl
  | inr i =>
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact congrArg (fun a : fixedField q => (a : q.Extension 2)) (congrFun hn j)
    · change v.val (Sum.inr (last n)) = w.val (Sum.inr (last n))
      rw [fixed_last_pair (q.Extension 2) n _ v.val v.property,
        fixed_last_pair (q.Extension 2) n _ w.val w.property]
      exact congrArg (definingFieldAutomorphism q 2) hl

instance fixedVectors_finite (n : ℕ) (q : CFSG.PrimePower) :
    Finite (fixedVectors n q) :=
  Finite.of_injective (coordinateEncoding n q) (coordinateEncoding_injective n q)

theorem fixedVectors_card_le (n : ℕ) (q : CFSG.PrimePower) :
    Nat.card (fixedVectors n q) ≤ q.order ^ (2 * (n + 2)) := by
  have h := Nat.card_le_card_of_injective (coordinateEncoding n q)
    (coordinateEncoding_injective n q)
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin,
    fixedField_card, CFSGTwistedANaturalMatrices.extension_two_card] at h
  have he : q.order ^ (n + 1) * (q.order ^ (n + 1) * q.order ^ 2) =
      q.order ^ (2 * (n + 2)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  exact h.trans_eq he

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorCardinality
