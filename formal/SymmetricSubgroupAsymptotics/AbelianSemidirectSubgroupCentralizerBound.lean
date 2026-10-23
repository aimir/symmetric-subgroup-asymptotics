import SymmetricSubgroupAsymptotics.AbelianActionCentralizerClassBound
import SymmetricSubgroupAsymptotics.SemidirectSubgroupOverKernel
import SymmetricSubgroupAsymptotics.BlockKernelClassBound

/-! A fixed-point and centralizer budget controls every subgroup of
the same abelian semidirect product. Both branches retain the literal
projected complement; no subgroup class-count monotonicity is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AbelianSemidirectSubgroupCentralizerBound
open SemidirectSubgroupOverKernel

variable {N H : Type*} [CommGroup N] [Group H] [Finite N] [Finite H]

theorem kernel_card_le_intersection (φ : H →* MulAut N)
    (L : Subgroup (N ⋊[φ] H)) :
    Nat.card (((SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype).ker) ≤
      Nat.card (L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))) := by
  let f := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
  let K := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))
  let a : f.ker → K := fun x => ⟨x.val.val.left,by
    change SemidirectProduct.inl x.val.val.left ∈ L
    have hr : x.val.val.right=1 := x.property
    have he : (SemidirectProduct.inl x.val.val.left : N ⋊[φ] H)=x.val.val := by
      apply SemidirectProduct.ext
      · rfl
      · exact hr.symm
    rw [he]
    exact x.val.property⟩
  apply Nat.card_le_card_of_injective a
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact congrArg (fun z : K => z.val) he
  · exact (show x.val.val.right=1 from x.property).trans
      (show y.val.val.right=1 from y.property).symm

theorem subgroup_class_card_le (φ : H →* MulAut N) (d c : ℕ)
    (hfixed : ∀h : H, h ≠ 1 → Nat.card {n : N // φ h n=n} ≤ d)
    (hcent : ∀h : H, h ≠ 1 → Nat.card {k : H // Commute h k} ≤ c)
    (hproper : ∀K : Subgroup N, K ≠ ⊤ → Nat.card K ≤ d)
    (hcapacity : Nat.card N ≤ d*c) (L : Subgroup (N ⋊[φ] H)) :
    Nat.card (ConjClasses L) ≤ d*(c+1) := by
  letI : Finite (N ⋊[φ] H) := Finite.of_equiv (N×H) SemidirectProduct.equivProd.symm
  let K : Subgroup N := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] H))
  by_cases hK : K=⊤
  · have hfull : ∀n : N, SemidirectProduct.inl n ∈ L := by
      intro n
      have hn : n ∈ K := by rw [hK]; trivial
      exact hn
    let e := overKernelEquiv φ L hfull
    let R := Projected φ L
    let ψ : R →* MulAut N := φ.comp R.subtype
    letI : Finite (N ⋊[ψ] R) := Finite.of_equiv L e.toEquiv
    have hfixR (r : R) (hr : r ≠ 1) : Nat.card {n : N // ψ r n=n} ≤ d :=
      hfixed r.val (fun he => hr (Subtype.ext he))
    have hcentR (r : R) (hr : r ≠ 1) : Nat.card {s : R // Commute r s} ≤ c :=
      AbelianActionCentralizerClassBound.centralizer_card_le_of_injective
        R.subtype Subtype.val_injective c hcent r hr
    have hs := AbelianActionCentralizerClassBound.semidirect_class_card_le
      ψ d c hfixR hcentR hcapacity
    have hL : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (N ⋊[ψ] R)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    exact hL.trans hs
  · let f := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
    have hkcard : Nat.card f.ker ≤ d :=
      (kernel_card_le_intersection φ L).trans (hproper K hK)
    have hkclass : Nat.card (ConjClasses f.ker) ≤ d :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _)
        ConjClasses.mk_surjective).trans hkcard
    have hR : Nat.card (ConjClasses f.range) ≤ c+1 :=
      CentralizerClassBound.class_card_le_of_injective f.range.subtype
        Subtype.val_injective c hcent
    exact (conjugacyClass_card_le_kernel_mul_range f).trans (Nat.mul_le_mul hkclass hR)

end SymmetricSubgroupAsymptotics.AbelianSemidirectSubgroupCentralizerBound
