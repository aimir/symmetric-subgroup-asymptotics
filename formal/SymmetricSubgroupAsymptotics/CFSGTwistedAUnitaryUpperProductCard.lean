import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperFactorization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMiddleUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryParabolicFactorization
import Mathlib.SetTheory.Cardinal.Finite

/-! Exact product counting of the actual unitary upper subgroup.
The radical and smaller upper factor are recovered from the literal
middle entries, so their capacities are multiplied without losing a fibre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays

theorem middle_factor_eq_of_array_product_eq {K J : Type*} [CommRing K]
    [Fintype J] [DecidableEq J] (u v : arrayGroup (K := K) (J := J))
    (A B : (Matrix J J K)ˣ)
    (h : u.val * middleUnit A = v.val * middleUnit B) : A = B := by
  obtain ⟨w, x, b, hu⟩ := u.property
  obtain ⟨w', x', b', hv⟩ := v.property
  apply Units.ext
  ext i j
  have he := congrArg (fun M : (Matrix (Index J) (Index J) K)ˣ =>
    (M : Matrix (Index J) (Index J) K) (.inr (.inl i)) (.inr (.inl j))) h
  rw [hu, hv] at he
  change (upperArray w x b * middleArray (A : Matrix J J K))
      (.inr (.inl i)) (.inr (.inl j)) =
    (upperArray w' x' b' * middleArray (B : Matrix J J K))
      (.inr (.inl i)) (.inr (.inl j)) at he
  rw [upperArray_mul_middleArray, upperArray_mul_middleArray] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUpperUnipotent

def upperProduct (q : CFSG.PrimePower) (s : ℕ)
    (x : fixedRadical q s × naturalUnipotent s q) : naturalUnipotent (s + 2) q :=
  ⟨x.1.val.val * (naturalFixedMiddleHom q s (upperFixedHom q s x.2)).val,
    (naturalUnipotent (s + 2) q).mul_mem (fixedRadical_mem_upper q s x.1)
      (middleUnipotentHom q s x.2).property⟩

theorem upperProduct_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (upperProduct q s) := by
  rintro ⟨u, a⟩ ⟨v, b⟩ h
  have he := congrArg (upperFixedHom q (s + 2)) h
  change u.val * naturalFixedMiddleHom q s (upperFixedHom q s a) =
      v.val * naturalFixedMiddleHom q s (upperFixedHom q s b) at he
  have hm := congrArg (blockFixedMatrixHom q s) he
  simp only [map_mul, blockFixedMatrixHom_middle] at hm
  have hab : a = b := by
    apply Subtype.ext
    apply Subtype.ext
    exact middle_factor_eq_of_array_product_eq
      (radicalBlockHom q s u) (radicalBlockHom q s v) a.val.val b.val.val hm
  subst b
  have huv : u = v := Subtype.ext (mul_right_cancel he)
  exact Prod.ext huv rfl

theorem upperProduct_surjective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Surjective (upperProduct q s) := by
  intro g
  obtain ⟨r, hr⟩ := upper_radical_middle_factor q s g
  refine ⟨⟨r, middleUnipotentElement q s g⟩, ?_⟩
  apply Subtype.ext
  exact (congrArg Subtype.val hr).symm

def upperProductEquiv (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q s × naturalUnipotent s q ≃ naturalUnipotent (s + 2) q :=
  Equiv.ofBijective (upperProduct q s)
    ⟨upperProduct_injective q s, upperProduct_surjective q s⟩

theorem naturalUnipotent_card_step (q : CFSG.PrimePower) (s : ℕ) :
    Nat.card (naturalUnipotent (s + 2) q) =
      Nat.card (fixedRadical q s) * Nat.card (naturalUnipotent s q) := by
  rw [← Nat.card_congr (upperProductEquiv q s), Nat.card_prod]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
