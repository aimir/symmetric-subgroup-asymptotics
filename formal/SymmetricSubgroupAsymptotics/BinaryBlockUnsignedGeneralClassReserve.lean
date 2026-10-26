import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedKernelCoordinates
import SymmetricSubgroupAsymptotics.CyclicOrbitCountNonSwapDeficit
import SymmetricSubgroupAsymptotics.SubnormalSmallFibreTopClassBound

/-! A variable actual top class budget B>=11 pays every unsigned binary
extension with no transpositions. The actual identity reserve costs one
extra top unit; quotient images of order below four cost at most12 units.
Original subnormal images, kernel correlations and nonsplit extensions
are retained. No model or global class bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
open OriginalBlockClassBound BinaryBlockUnsignedKernelCoordinates

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]
    (b : Ω→X) (hb : ∀ (a : A) (ω : Ω),b (a•ω)=a•b ω)

omit [Finite A] [Finite X] in
private theorem quotientHom_injective :
    Function.Injective (quotientHom (A:=A) (X:=X)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H a =>
    exact (QuotientGroup.eq_one_iff a).mpr hq

include hb

/-- The small quotient branch is absorbed by the same reserve; no
subnormal-image trichotomy or actual-image enlargement is used. -/
theorem class_card_le_class_budget_add_one_mul
    (hsmall : ∀x,Nat.card (originalBlockFibre b x)≤2)
    (hn : 2≤Nat.card X)
    (B : ℕ) (hB : 11≤B)
    (htop : Nat.card (ConjClasses (Top (A:=A) (X:=X)))≤B)
    (hns : ∀a:A,¬(topMap (A:=A) (X:=X) a).IsSwap) :
    Nat.card (ConjClasses A)≤(B+1)*2^(Nat.card X-2) := by
  let N := Kernel (A:=A) (X:=X)
  letI : IsMulCommutative N :=
    BinaryBlockKernelAbelian.kernel_isMulCommutative b hb hsmall
  letI : MulAction (A ⧸ N) X := quotientAction (A:=A) (X:=X)
  have hclasses : Nat.card (ConjClasses (A ⧸ N))≤B := by
    let e := QuotientGroup.quotientKerEquivRange (topMap (A:=A) (X:=X))
    exact (Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)).trans htop
  by_cases hQ : 4≤Nat.card (A ⧸ N)
  · have hcycles : ∀q:A ⧸ N,q≠1→
        Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers q) X)≤Nat.card X-2 := by
      intro q hq
      apply CyclicOrbitCountNonSwapDeficit.cyclic_orbit_card_le_sub_two q
      · intro h
        apply hq
        have hperm : quotientHom (A:=A) (X:=X) q=1 := by
          apply Equiv.ext
          intro x
          have he := congrArg (fun s : Equiv.Perm X=>s x) h
          change quotientHom (A:=A) (X:=X) q x=x at he
          exact he
        exact quotientHom_injective (hperm.trans
          (map_one (quotientHom (A:=A) (X:=X))).symm)
      · induction q using QuotientGroup.induction_on with
        | H a => exact hns a
    have hh := AbelianExtensionUnsignedPermutationClassBound.class_card_le_class_add_one_mul
      N (coordinates b hb) (coordinates_injective b hb hsmall)
      (quotient_intertwine b hb hsmall) hQ hcycles
    exact hh.trans (Nat.mul_le_mul_right _ (by omega))
  · have hQc : Nat.card (ConjClasses (A ⧸ N))≤3 :=
      (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans (by omega)
    have hNc : Nat.card (ConjClasses N)≤2^Nat.card X :=
      (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
        (BinaryBlockKernelAbelian.kernel_card_le_power b hb hsmall)
    calc
      _≤Nat.card (ConjClasses N)*Nat.card (ConjClasses (A ⧸ N)) :=
        conjugacyClass_card_le_normal_mul_quotient N
      _≤2^Nat.card X*3 := Nat.mul_le_mul hNc hQc
      _=12*2^(Nat.card X-2) := by
        have he : Nat.card X=(Nat.card X-2)+2 := by omega
        conv_lhs => rw [he,pow_add]
        ring
      _≤(B+1)*2^(Nat.card X-2) := Nat.mul_le_mul_right _ (by omega)

/-- The same bound for an arbitrary actual subnormal source. Its top is
identified with its image under the original surjective top map, so only
that actual image receives the original subnormal class budget. -/
theorem subnormal_class_card_le_class_budget_add_one_mul
    (hsmall : ∀x,Nat.card (originalBlockFibre b x)≤2)
    (hn : 2≤Nat.card X)
    (B : ℕ) (hB : 11≤B)
    (htop : ∀L:Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal→
      Nat.card (ConjClasses L)≤B)
    (hns : ∀a:A,¬(topMap (A:=A) (X:=X) a).IsSwap)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)≤(B+1)*2^(Nat.card X-2) := by
  have hbH : ∀ (g:H) (ω:Ω),b (g•ω)=g•b ω := fun g ω=>hb g.val ω
  let f : A→*Top (A:=A) (X:=X) := (topMap (A:=A) (X:=X)).rangeRestrict
  let M : Subgroup (Top (A:=A) (X:=X)) := H.map f
  have hM : M.IsSubnormal := hH.map (MonoidHom.rangeRestrict_surjective _)
  have hr : M.map (Top (A:=A) (X:=X)).subtype=Top (A:=H) (X:=X) := by
    ext σ
    constructor
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨g,hg,he⟩ := hu
      exact ⟨⟨g,hg⟩,congrArg Subtype.val he⟩
    · rintro ⟨g,rfl⟩
      exact ⟨f g.val,⟨g.val,g.property,rfl⟩,rfl⟩
  let e := (M.equivMapOfInjective (Top (A:=A) (X:=X)).subtype
    Subtype.val_injective).trans (MulEquiv.subgroupCongr hr)
  have hbudget : Nat.card (ConjClasses (Top (A:=H) (X:=X)))≤B :=
    (Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
      (ConjClasses.map_surjective e.surjective)).trans (htop M hM)
  exact class_card_le_class_budget_add_one_mul b hbH hsmall hn B hB hbudget (fun g=>hns g.val)

end SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
