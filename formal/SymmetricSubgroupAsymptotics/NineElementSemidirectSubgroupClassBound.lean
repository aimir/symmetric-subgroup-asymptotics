import SymmetricSubgroupAsymptotics.OrderNineAutomorphismClassBound
import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import SymmetricSubgroupAsymptotics.SemidirectSubgroupOverKernel
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Linarith

/-! Every subgroup of an actual semidirect product with a nine-element
abelian kernel and faithful complement action has at most54 classes.
Proper kernel intersections have at most3 elements, so class extension
uses the actual projected group's at most10 classes. A full intersection
gives the literal semidirect product and the proved fixed-space bound.
No subgroup class monotonicity or supplied splitting is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassBound
open SemidirectSubgroupOverKernel

variable {N H : Type*} [CommGroup N] [Group H]

theorem proper_subgroup_card_le_three [Finite N] (hN : Nat.card N = 9)
    (K : Subgroup N) (hK : K ≠ ⊤) : Nat.card K ≤ 3 := by
  have hd : Nat.card K ∣ (3 : ℕ)^2 := by
    simpa only [hN, show (3 : ℕ)^2=9 by decide] using K.card_subgroup_dvd_card
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hi1 : i ≤ 1 := by
    by_contra hn
    have hi2 : i=2 := by omega
    apply hK
    apply K.eq_top_of_card_eq
    simpa only [he, hi2, show (3 : ℕ)^2=9 by decide] using hN.symm
  calc
    Nat.card K = 3^i := he
    _ ≤ 3^1 := Nat.pow_le_pow_right (by decide) hi1
    _ = 3 := pow_one _

private theorem kernel_card_le_intersection [Finite N]
    (φ : H →* MulAut N) (L : Subgroup (N ⋊[φ] H)) :
    Nat.card (((SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype).ker) ≤
      Nat.card (L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))) := by
  let f := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
  let K := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))
  let d : f.ker → K := fun x => ⟨x.val.val.left, by
    change SemidirectProduct.inl x.val.val.left ∈ L
    have hr : x.val.val.right=1 := x.property
    have he : (SemidirectProduct.inl x.val.val.left : N ⋊[φ] H)=x.val.val := by
      apply SemidirectProduct.ext
      · rfl
      · exact hr.symm
    rw [he]
    exact x.val.property⟩
  apply Nat.card_le_card_of_injective d
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact congrArg (fun z : K => z.val) he
  · exact (show x.val.val.right=1 from x.property).trans
      (show y.val.val.right=1 from y.property).symm

theorem subgroup_class_card_le_fiftyFour [Finite N] [Finite H]
    (hN : Nat.card N = 9) (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] H)) : Nat.card (ConjClasses L) ≤ 54 := by
  letI : Finite (N ⋊[φ] H) := Finite.of_equiv (N×H) SemidirectProduct.equivProd.symm
  by_cases hcyclic : IsCyclic N
  · letI : IsCyclic N := hcyclic
    have hAut : Nat.card (MulAut N)=6 := by
      rw [IsCyclic.card_mulAut, hN]
      decide +kernel
    have hH : Nat.card H ≤ 6 := (Nat.card_le_card_of_injective φ hφ).trans_eq hAut
    have horder : Nat.card (N ⋊[φ] H) ≤ 54 := by
      rw [SemidirectProduct.card, hN]
      omega
    exact ((Nat.card_le_card_of_surjective (@ConjClasses.mk L _)
      ConjClasses.mk_surjective).trans L.card_le_card_group).trans horder
  · let K : Subgroup N := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))
    by_cases hK : K=⊤
    · have hfull : ∀ n : N, SemidirectProduct.inl n ∈ L := by
        intro n
        have hn : n ∈ K := by rw [hK]; trivial
        exact hn
      let e := overKernelEquiv φ L hfull
      let R := Projected φ L
      let ψ : R →* MulAut N := φ.comp R.subtype
      have hψ : Function.Injective ψ := hφ.comp Subtype.val_injective
      letI : Finite (N ⋊[ψ] R) := Finite.of_equiv L e.toEquiv
      have hR : Nat.card (ConjClasses R) ≤ 10 :=
        OrderNineAutomorphismClassBound.class_card_le_ten hN hcyclic ψ hψ
      have hs := AbelianActionClassBound.class_card_le_fixed ψ 3
        (fun r hr => OrderNineAutomorphismClassBound.fixed_card_le_three hN hcyclic ψ hψ r hr)
      rw [hN] at hs
      have hL : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (N ⋊[ψ] R)) :=
        Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
          (ConjClasses.map_surjective e.symm.surjective)
      omega
    · let f := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
      have hkcard : Nat.card f.ker ≤ 3 :=
        (kernel_card_le_intersection φ L).trans (proper_subgroup_card_le_three hN K hK)
      have hkclass : Nat.card (ConjClasses f.ker) ≤ 3 :=
        (Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _)
          ConjClasses.mk_surjective).trans hkcard
      let ψ : f.range →* MulAut N := φ.comp f.range.subtype
      have hψ : Function.Injective ψ := hφ.comp Subtype.val_injective
      have hR : Nat.card (ConjClasses f.range) ≤ 10 :=
        OrderNineAutomorphismClassBound.class_card_le_ten hN hcyclic ψ hψ
      exact (conjugacyClass_card_le_kernel_mul_range f).trans
        ((Nat.mul_le_mul hkclass hR).trans (by decide))

end SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassBound
