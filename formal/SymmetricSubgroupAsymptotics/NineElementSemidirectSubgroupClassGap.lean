import SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassBound
import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import SymmetricSubgroupAsymptotics.SemidirectSubgroupOverKernel
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Linarith

/-! Every subgroup of a faithful semidirect product with a nine-element
abelian kernel has at most 39 classes. The literal restriction of each
nonidentity complement element fixes a proper subgroup of order at most
three. The full-intersection and proper-intersection counts are combined
without assuming subgroup class monotonicity or a supplied splitting. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassGap
open SemidirectSubgroupOverKernel

variable {N H : Type*} [CommGroup N] [Group H]

theorem complement_class_card_le_ten [Finite N] [Finite H]
    (hN : Nat.card N = 9) (φ : H →* MulAut N) (hφ : Function.Injective φ) :
    Nat.card (ConjClasses H) ≤ 10 := by
  by_cases hc : IsCyclic N
  · letI : IsCyclic N := hc
    have hAut : Nat.card (MulAut N) = 6 := by
      rw [IsCyclic.card_mulAut,hN]
      decide +kernel
    exact ((Nat.card_le_card_of_surjective (@ConjClasses.mk H _)
      ConjClasses.mk_surjective).trans
      (Nat.card_le_card_of_injective φ hφ)).trans (by omega)
  · exact OrderNineAutomorphismClassBound.class_card_le_ten hN hc φ hφ

theorem fixed_card_le_three [Finite N] (hN : Nat.card N = 9)
    (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (h : H) (hh : h ≠ 1) : Nat.card {n : N // φ h n = n} ≤ 3 := by
  let F := (φ h).toMonoidHom.eqLocus (MonoidHom.id N)
  have hF : F ≠ ⊤ := by
    intro he
    apply hh
    apply hφ
    rw [φ.map_one]
    apply MulEquiv.ext
    intro n
    have hn : n ∈ F := by rw [he]; trivial
    exact hn
  exact NineElementSemidirectSubgroupClassBound.proper_subgroup_card_le_three hN F hF

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

theorem subgroup_class_card_le_thirtyNine [Finite N] [Finite H]
    (hN : Nat.card N = 9) (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] H)) : Nat.card (ConjClasses L) ≤ 39 := by
  letI : Finite (N ⋊[φ] H) := Finite.of_equiv (N×H) SemidirectProduct.equivProd.symm
  let K : Subgroup N := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))
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
      complement_class_card_le_ten hN ψ hψ
    have hs := AbelianActionClassBound.class_card_le_fixed ψ 3
      (fun r hr => fixed_card_le_three hN ψ hψ r hr)
    rw [hN] at hs
    have hL : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (N ⋊[ψ] R)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    omega
  · let f := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
    have hkcard : Nat.card f.ker ≤ 3 :=
      (kernel_card_le_intersection φ L).trans (NineElementSemidirectSubgroupClassBound.proper_subgroup_card_le_three hN K hK)
    have hkclass : Nat.card (ConjClasses f.ker) ≤ 3 :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _)
        ConjClasses.mk_surjective).trans hkcard
    let ψ : f.range →* MulAut N := φ.comp f.range.subtype
    have hψ : Function.Injective ψ := hφ.comp Subtype.val_injective
    have hR : Nat.card (ConjClasses f.range) ≤ 10 :=
      complement_class_card_le_ten hN ψ hψ
    exact (conjugacyClass_card_le_kernel_mul_range f).trans
      ((Nat.mul_le_mul hkclass hR).trans (by decide))
end SymmetricSubgroupAsymptotics.NineElementSemidirectSubgroupClassGap
