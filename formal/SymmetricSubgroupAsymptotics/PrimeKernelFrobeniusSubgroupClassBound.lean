import SymmetricSubgroupAsymptotics.FrobeniusAbelianClassBound
import SymmetricSubgroupAsymptotics.SemidirectSubgroupOverKernel
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! All subgroups of an abelian-by-abelian Frobenius group with prime
kernel have at most |N| classes. The actual kernel intersection is
trivial or whole; both branches retain the actual projected subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimeKernelFrobeniusSubgroupClassBound
open SemidirectSubgroupOverKernel

variable {N H : Type*} [CommGroup N] [CommGroup H] [Finite N] [Finite H]
    [Nontrivial N] [hprime : Fact (Nat.card N).Prime] (φ : H →* MulAut N)
    (hfree : ∀ (h : H), h≠1 → ∀ n : N, φ h n=n → n=1)

include hfree hprime in
theorem subgroup_class_card_le_kernel (L : Subgroup (N ⋊[φ] H)) :
    Nat.card (ConjClasses L) ≤ Nat.card N := by
  letI : Finite (N ⋊[φ] H) := Finite.of_equiv (N × H) SemidirectProduct.equivProd.symm
  let K : Subgroup N := L.comap (SemidirectProduct.inl : N →* N ⋊[φ] H)
  rcases K.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · have hproj := rightHom_injective_of_comap_bot φ L hbot
    have hclass : Nat.card (ConjClasses L) ≤ Nat.card L :=
      Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective
    have horder : Nat.card L ≤ Nat.card H := Nat.card_le_card_of_injective
      ((SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype) hproj
    exact ((hclass.trans horder).trans
      (FrobeniusComplementCard.complement_card_le_pred φ hfree)).trans (Nat.sub_le _ _)
  · have hN : ∀ n : N, SemidirectProduct.inl n ∈ L := by
      intro n
      have hn : n ∈ K := by rw [htop]; exact Subgroup.mem_top n
      exact hn
    let e := overKernelEquiv φ L hN
    letI : Finite (N ⋊[φ.comp (Projected φ L).subtype] Projected φ L) :=
      Finite.of_equiv L e.toEquiv
    have hclass : Nat.card (ConjClasses L) ≤
        Nat.card (ConjClasses (N ⋊[φ.comp (Projected φ L).subtype] Projected φ L)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    have hfreeC : ∀ c : Projected φ L, c≠1 → ∀ n : N,
        (φ.comp (Projected φ L).subtype) c n=n → n=1 := by
      intro c hc n hn
      apply hfree c.val _ n hn
      intro he
      exact hc (Subtype.ext he)
    exact hclass.trans (FrobeniusAbelianClassBound.class_card_le_kernel
      (φ.comp (Projected φ L).subtype) hfreeC)

end SymmetricSubgroupAsymptotics.PrimeKernelFrobeniusSubgroupClassBound
