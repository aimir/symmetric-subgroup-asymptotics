import SymmetricSubgroupAsymptotics.FiniteBinaryFiveLinearClassBound
import SymmetricSubgroupAsymptotics.AbelianActionClassBound
import SymmetricSubgroupAsymptotics.SemidirectSubgroupOverKernel
import SymmetricSubgroupAsymptotics.BlockKernelClassBound
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Subgroup.Finite

/-! All subgroups of a semidirect product with an actual binary
five-dimensional translation module satisfy a uniform class bound.
The proper-kernel branch retains the actual projected complement;
the full-kernel branch uses its literal semidirect equivalence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryFiveElementSemidirectClassBound
open SemidirectSubgroupOverKernel

variable {N H : Type*} [CommGroup N] [Group H]

theorem proper_subgroup_card_le_sixteen [Finite N] (hN : Nat.card N=32)
    (K : Subgroup N) (hK : K ≠ ⊤) : Nat.card K ≤ 16 := by
  have hd : Nat.card K ∣ (2 : ℕ)^5 := by
    simpa only [hN, show (2 : ℕ)^5=32 by decide] using K.card_subgroup_dvd_card
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hi4 : i ≤ 4 := by
    by_contra hn
    have hi5 : i=5 := by omega
    apply hK
    apply K.eq_top_of_card_eq
    simpa only [he, hi5, show (2 : ℕ)^5=32 by decide] using hN.symm
  calc
    Nat.card K = 2^i := he
    _ ≤ 2^4 := Nat.pow_le_pow_right (by decide) hi4
    _ = 16 := by decide

variable {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

def automorphismLinear : MulAut N →* (Additive N ≃ₗ[ZMod p] Additive N) where
  toFun a := { a.toAdditive with map_smul' := fun c x => ZMod.map_smul a.toAdditive c x }
  map_one' := by ext x; rfl
  map_mul' _a _b := by ext x; rfl

theorem automorphismLinear_injective :
    Function.Injective (automorphismLinear (N := N) (p := p)) := by
  intro a b he
  apply MulEquiv.ext
  intro x
  exact congrArg Additive.toMul (DFunLike.congr_fun he (Additive.ofMul x))

theorem complement_class_card_le [Finite N] [Finite H]
    (hp : p=2) (hN : Nat.card N=32)
    (φ : H →* MulAut N) (hφ : Function.Injective φ) :
    Nat.card (ConjClasses H) ≤ 1015809 := by
  let ρ : H →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp hφ
  have hA : Nat.card (Additive N)=32 := hN
  have hK : Nat.card (ZMod p)=2 := (Nat.card_zmod p).trans hp
  exact FiniteBinaryFiveLinearClassBound.class_card_le
    (K := ZMod p) (V := Additive N) hK hA ρ hρ

theorem fixed_card_le_sixteen [Finite N]
    (hp : p=2) (hN : Nat.card N=32)
    (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (h : H) (hh : h ≠ 1) : Nat.card {n : N // φ h n=n} ≤ 16 := by
  let ρ : H →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp φ
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp hφ
  have he : ρ h ≠ 1 := fun he => hh (hρ (he.trans ρ.map_one.symm))
  let e : {n : N // φ h n=n} ≃ {v : Additive N // ρ h v=v} := {
    toFun := fun n => ⟨Additive.ofMul n.val, congrArg Additive.ofMul n.property⟩
    invFun := fun v => ⟨v.val.toMul, congrArg Additive.toMul v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hA : Nat.card (Additive N)=32 := hN
  have hK : Nat.card (ZMod p)=2 := (Nat.card_zmod p).trans hp
  exact (Nat.card_congr e).trans_le
    (FiniteBinaryFiveSpaceBounds.fixed_card_le_sixteen
      (K := ZMod p) (V := Additive N) hK hA (ρ h) he)

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

theorem subgroup_class_card_le [Finite N] [Finite H]
    (hp : p=2) (hN : Nat.card N=32)
    (φ : H →* MulAut N) (hφ : Function.Injective φ)
    (L : Subgroup (N ⋊[φ] H)) : Nat.card (ConjClasses L) ≤ 16252976 := by
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
    have hR := complement_class_card_le hp hN ψ hψ
    have hs := AbelianActionClassBound.class_card_le_fixed ψ 16
      (fun r hr => fixed_card_le_sixteen hp hN ψ hψ r hr)
    rw [hN] at hs
    have hL : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses (N ⋊[ψ] R)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    omega
  · let f := (SemidirectProduct.rightHom : (N ⋊[φ] H) →* H).comp L.subtype
    have hkcard : Nat.card f.ker ≤ 16 :=
      (kernel_card_le_intersection φ L).trans (proper_subgroup_card_le_sixteen hN K hK)
    have hkclass : Nat.card (ConjClasses f.ker) ≤ 16 :=
      (Nat.card_le_card_of_surjective (@ConjClasses.mk f.ker _)
        ConjClasses.mk_surjective).trans hkcard
    let ψ : f.range →* MulAut N := φ.comp f.range.subtype
    have hψ : Function.Injective ψ := hφ.comp Subtype.val_injective
    have hR := complement_class_card_le hp hN ψ hψ
    exact (conjugacyClass_card_le_kernel_mul_range f).trans
      ((Nat.mul_le_mul hkclass hR).trans (by decide))

end SymmetricSubgroupAsymptotics.BinaryFiveElementSemidirectClassBound
