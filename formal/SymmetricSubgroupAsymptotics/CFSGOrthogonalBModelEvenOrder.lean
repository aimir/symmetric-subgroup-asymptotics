import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBChainWord
import SymmetricSubgroupAsymptotics.CFSGSerreCharacteristicTwoParity
import Mathlib.Algebra.CharP.Basic

/-! Even cardinality of every original simple B-transpose model.
Odd characteristic uses the actual quadratic-root projective realization;
characteristic two uses original surviving root involutions directly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley

theorem serreTypeB_even_card_of_two_ne_zero (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0)
    [IsSimpleGroup (Projective (CartanMatrix.B (r+2)).transpose K)] :
    Even (Nat.card (Projective (CartanMatrix.B (r+2)).transpose K)) := by
  rw [Nat.card_congr (serreProjectiveEquivElementaryProjective K (r+1) h2).toEquiv]
  exact elementaryProjective_even_card K r h2

theorem serreTypeB_even_card (K : Type) [Field K] (r : ℕ)
    [IsSimpleGroup (Projective (CartanMatrix.B (r+2)).transpose K)] :
    Even (Nat.card (Projective (CartanMatrix.B (r+2)).transpose K)) := by
  by_cases h2 : (2:K)=0
  · letI : CharP K 2 := (CharP.charP_iff_prime_eq_zero (R:=K) (by decide : Nat.Prime 2)).mpr h2
    exact CFSGSerreCharacteristicTwoParity.projective_even_card (CartanMatrix.B (r+2)).transpose K
  · exact serreTypeB_even_card_of_two_ne_zero K r h2

theorem typeB_even_card (r : ℕ) (q : CFSG.PrimePower) (hr : 2≤r)
    [IsSimpleGroup (CFSG.Models.B r q)] : Even (Nat.card (CFSG.Models.B r q)) := by
  have he : r-2+2=r := by omega
  letI : IsSimpleGroup (Projective (CartanMatrix.B (r-2+2)).transpose q.Field) := by
    rw [he]
    infer_instance
  have h := serreTypeB_even_card q.Field (r-2)
  rw [he] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
