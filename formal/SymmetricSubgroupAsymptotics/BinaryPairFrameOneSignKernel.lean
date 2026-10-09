import SymmetricSubgroupAsymptotics.BinaryPairFrameSignIsotypes

/-!
# The one-sign kernel of a transitive binary pair frame

If all literal pair coordinates carry the same character of the pair
kernel, every kernel element is a simultaneous flip.  The faithful bit
chart then bounds the kernel by `C₂`, and constant flip vectors are fixed by
every top permutation.  Thus the one-sign pair kernel is central in the
original source group.

This is stated for an arbitrary finite pair index.  In particular it can be
used at six, twelve, and eighteen blocks without repeating the four-block
diagonal argument.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X I : Type*} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- A unique realized coordinate character is equivalent to every kernel
element having the same bit on every pair. -/
theorem coordinateSign_count_eq_one_iff_bits_constant
    [Finite I] [Nonempty I] :
    Nat.card (CoordinateSign F) = 1 ↔
      ∀ (k : F.top.ker) (i j : I), F.bits k i = F.bits k j := by
  constructor
  · intro hone
    letI : Subsingleton (CoordinateSign F) :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    intro k i j
    exact congrFun (congrArg Subtype.val
      (Subsingleton.elim (coordinateSign F i) (coordinateSign F j))) k
  · intro hconstant
    let i0 : I := Classical.choice inferInstance
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨?_, ⟨coordinateSign F i0⟩⟩
    constructor
    intro chi psi
    obtain ⟨i, rfl⟩ := coordinateSign_surjective F chi
    obtain ⟨j, rfl⟩ := coordinateSign_surjective F psi
    apply Subtype.ext
    funext k
    exact hconstant k i j

/-- In the one-sign branch, evaluation at any one coordinate detects the
whole literal pair kernel. -/
theorem coordinateEvaluation_injective_of_sign_count_one
    [Finite I] [Nonempty I]
    (hone : Nat.card (CoordinateSign F) = 1) (i0 : I) :
    Function.Injective (fun k : F.top.ker => F.bits k i0) := by
  have hconstant :=
    (coordinateSign_count_eq_one_iff_bits_constant F).mp hone
  intro k l hkl
  apply F.bitsHom_injective
  apply congrArg Multiplicative.ofAdd
  funext i
  exact (hconstant k i i0).trans (hkl.trans (hconstant l i i0).symm)

/-- A one-sign pair kernel has order at most two. -/
theorem top_ker_card_le_two_of_sign_count_one
    [Finite X] [Finite I] [Nonempty I]
    (hone : Nat.card (CoordinateSign F) = 1) :
    Nat.card F.top.ker ≤ 2 := by
  let i0 : I := Classical.choice inferInstance
  calc
    Nat.card F.top.ker ≤ Nat.card (ZMod 2) :=
      Nat.card_le_card_of_injective (fun k : F.top.ker => F.bits k i0)
        (coordinateEvaluation_injective_of_sign_count_one F hone i0)
    _ = 2 := Nat.card_zmod 2

/-- If the literal pair kernel is nontrivial, the one-sign bound is exact. -/
theorem top_ker_card_eq_two_of_sign_count_one
    [Finite X] [Finite I] [Nonempty I]
    (hone : Nat.card (CoordinateSign F) = 1)
    (hK : F.top.ker ≠ ⊥) :
    Nat.card F.top.ker = 2 := by
  have hnontrivial : Nontrivial F.top.ker := by
    exact F.top.ker.nontrivial_iff_ne_bot.mpr hK
  have hlower : 2 ≤ Nat.card F.top.ker :=
    Finite.one_lt_card_iff_nontrivial.mpr hnontrivial
  exact Nat.le_antisymm (top_ker_card_le_two_of_sign_count_one F hone) hlower

/-- The simultaneous-flip kernel is central in the original pair group. -/
theorem top_ker_le_center_of_sign_count_one
    [Finite I] [Nonempty I]
    (hone : Nat.card (CoordinateSign F) = 1) :
    F.top.ker ≤ Subgroup.center G := by
  have hconstant :=
    (coordinateSign_count_eq_one_iff_bits_constant F).mp hone
  intro k hk
  let k' : F.top.ker := ⟨k, hk⟩
  rw [Subgroup.mem_center_iff]
  intro u
  have hkfixed : MulAut.conjNormal u k' = k' := by
    apply F.bitsHom_injective
    apply congrArg Multiplicative.ofAdd
    funext i
    rw [F.bits_conjNormal]
    exact hconstant k' ((F.top u)⁻¹ i) i
  have hkfixed' := congrArg Subtype.val hkfixed
  change u * k * u⁻¹ = k at hkfixed'
  calc
    k * u = (u * k * u⁻¹) * u := by rw [hkfixed']
    _ = u * k := by simp [mul_assoc]

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
