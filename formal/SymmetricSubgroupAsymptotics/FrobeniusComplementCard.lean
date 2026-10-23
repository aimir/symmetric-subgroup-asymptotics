import Mathlib.Algebra.Group.End
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.Card

/-! A free automorphism action on nonidentity elements bounds the ACTUAL
complement by the number of nonidentity kernel elements. No cyclicity,
field structure, or transitivity of the complement is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FrobeniusComplementCard

variable {N H : Type*} [Group N] [Group H] (φ : H →* MulAut N)
    (hfree : ∀ (h : H), h≠1 → ∀ n : N, φ h n=n → n=1)

include hfree in
theorem orbitParameter_injective (n : N) (hn : n≠1) :
    Function.Injective (fun h : H => φ h n) := by
  intro h k he
  change φ h n=φ k n at he
  by_cases hrel : k⁻¹*h=1
  · exact (inv_mul_eq_one.mp hrel).symm
  · have hfix : φ (k⁻¹*h) n=n := by
      rw [map_mul,map_inv]
      change (φ k).symm ((φ h) n)=n
      rw [he,MulEquiv.symm_apply_apply]
    exact False.elim (hn (hfree (k⁻¹*h) hrel n hfix))

include hfree in
theorem complement_card_le_pred [Finite N] [Finite H] [Nontrivial N] :
    Nat.card H ≤ Nat.card N-1 := by
  obtain ⟨n,hn⟩ := exists_ne (1 : N)
  let f : H → {x : N // x≠1} := fun h => ⟨φ h n,by
    intro he
    apply hn
    apply (φ h).injective
    simpa only [map_one] using he⟩
  have hf : Function.Injective f := by
    intro h k he
    exact orbitParameter_injective φ hfree n hn (congrArg Subtype.val he)
  have hc : Nat.card {x : N // x≠1}=Nat.card N-1 := by
    letI : Fintype N := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl (fun x : N => x=1),
      Fintype.card_subtype_eq,Nat.card_eq_fintype_card]
  exact (Nat.card_le_card_of_injective f hf).trans_eq hc

end SymmetricSubgroupAsymptotics.FrobeniusComplementCard
