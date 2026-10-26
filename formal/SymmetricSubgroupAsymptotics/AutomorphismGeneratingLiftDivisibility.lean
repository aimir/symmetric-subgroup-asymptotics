import SymmetricSubgroupAsymptotics.AutomorphismQuotientKernelCardinality
import Mathlib.GroupTheory.GroupAction.Quotient

/-! A quotient-trivial automorphism group acts freely on the lifts of a
generating quotient tuple, provided every lift generates the original
group. The full lift set, rather than the orbit of one tuple, gives actual
cardinal divisibility. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AutomorphismGeneratingLiftDivisibility

variable {N Q ι : Type*} [Group N] [Group Q]

def Lift (π : N →* Q) (g : ι → N) :=
  {x : ι → N // ∀ i, π (x i) = π (g i)}

def liftEquivKernel (π : N →* Q) (g : ι → N) : Lift π g ≃ (ι → π.ker) where
  toFun x i := ⟨x.val i * (g i)⁻¹, by
    change π (x.val i * (g i)⁻¹) = 1
    rw [π.map_mul,π.map_inv,x.property i,mul_inv_cancel]⟩
  invFun k := ⟨fun i => (k i).val * g i, by
    intro i
    rw [π.map_mul,(k i).property,one_mul]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact inv_mul_cancel_right (x.val i) (g i)
  right_inv k := by
    funext i
    apply Subtype.ext
    exact mul_inv_cancel_right (k i).val (g i)

@[reducible] def liftAction (π : N →* Q) (g : ι → N) (A : Subgroup (MulAut N))
    (htrivial : ∀ (a : A) (n : N), π (a.val n) = π n) :
    MulAction A (Lift π g) where
  smul a x := ⟨fun i => a.val (x.val i),fun i => (htrivial a (x.val i)).trans (x.property i)⟩
  one_smul x := by
    apply Subtype.ext
    funext i
    rfl
  mul_smul a b x := by
    apply Subtype.ext
    funext i
    rfl

theorem card_dvd_kernel_pow [Finite N] [Fintype ι]
    (π : N →* Q) (g : ι → N)
    (hlift : ∀ x : Lift π g, Subgroup.closure (Set.range x.val) = ⊤)
    (A : Subgroup (MulAut N))
    (htrivial : ∀ (a : A) (n : N), π (a.val n) = π n) :
    Nat.card A ∣ (Nat.card π.ker) ^ Fintype.card ι := by
  letI : Finite (MulAut N) := Finite.of_injective
    (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective
  letI : MulAction A (Lift π g) := liftAction π g A htrivial
  have hfree : ∀ x : Lift π g, MulAction.stabilizer A x = ⊥ := by
    intro x
    apply bot_unique
    intro a ha
    change a • x = x at ha
    have hmaps : a.val.toMonoidHom = MonoidHom.id N := by
      apply MonoidHom.eq_of_eqOn_dense (hlift x)
      rintro n ⟨i,rfl⟩
      exact congrArg (fun z : Lift π g => z.val i) ha
    have he : a = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro n
      exact DFunLike.congr_fun hmaps n
    exact Subgroup.mem_bot.mpr he
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree)
  rw [Nat.card_prod] at hcard
  have hd : Nat.card A ∣ Nat.card (Lift π g) := by
    rw [hcard]
    exact dvd_mul_left _ _
  have hcount : Nat.card (Lift π g) = (Nat.card π.ker) ^ Fintype.card ι := by
    rw [Nat.card_congr (liftEquivKernel π g),Nat.card_fun,Nat.card_eq_fintype_card (α := ι)]
  exact hcount ▸ hd

end SymmetricSubgroupAsymptotics.AutomorphismGeneratingLiftDivisibility
