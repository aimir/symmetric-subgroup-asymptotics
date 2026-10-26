import SymmetricSubgroupAsymptotics.TernaryFourTransitiveAffineClassBound

/-! An original faithful source in S3 wr S4 with transitive projected
top of order at most eight has at most360 classes. Both the top action
and its actual range are transported through the exact affine chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourBinaryTopWreathClassBound
open TernaryWreathAffineSemidirectEquiv TernaryFourAffineProperKernelClassBound

theorem class_card_le_threeSixty {A : Type} [Group A] [Finite A]
    (f : A →* Wreath (Fin 4)) (hf : Function.Injective f)
    (htrans : ∀ i j : Fin 4,∃g : A,(f g).right i=j)
    (hQ : Nat.card
      ((PermutationalWreathProduct.rightHom : Wreath (Fin 4) →* Equiv.Perm (Fin 4)).comp f).range≤8) :
    Nat.card (ConjClasses A)≤360 := by
  let g : A →* Affine (Fin 4) := (equiv (Fin 4)).toMonoidHom.comp f
  let t := (PermutationalWreathProduct.rightHom : Wreath (Fin 4) →* Equiv.Perm (Fin 4)).comp f
  have hg : Function.Injective g := (equiv (Fin 4)).injective.comp hf
  let e : A ≃* g.range := MulEquiv.ofBijective g.rangeRestrict
    ⟨fun _ _ h => hg (congrArg Subtype.val h),g.rangeRestrict_surjective⟩
  letI : Finite g.range := Finite.of_equiv A e.toEquiv
  let ψ := originalTopHom g.range
  have hcomp : ψ.comp g.rangeRestrict=t := by
    apply MonoidHom.ext
    intro x
    change ((equiv (Fin 4)) (f x)).right.right=(f x).right
    exact equiv_preserves_original_top (Fin 4) (f x)
  have hrange : ψ.range=t.range := by
    ext s
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨x,hx⟩ := g.rangeRestrict_surjective u
      have he := DFunLike.congr_fun hcomp x
      exact ⟨x,he.symm.trans ((congrArg ψ hx).trans hu)⟩
    · rintro ⟨x,hx⟩
      exact ⟨g.rangeRestrict x,(DFunLike.congr_fun hcomp x).trans hx⟩
  have htop : ∀ i j : Fin 4,∃x : g.range,originalTopHom g.range x i=j := by
    intro i j
    obtain ⟨x,hx⟩ := htrans i j
    refine ⟨g.rangeRestrict x,?_⟩
    have he := congrArg (fun s : Equiv.Perm (Fin 4) => s i)
      (DFunLike.congr_fun hcomp x)
    exact he.trans hx
  have htopCard : Nat.card ψ.range≤8 := by rw [hrange]; exact hQ
  rw [conjugacyClass_card_congr e]
  exact TernaryFourTransitiveAffineClassBound.class_card_le_threeSixty g.range htop htopCard

end SymmetricSubgroupAsymptotics.TernaryFourBinaryTopWreathClassBound
