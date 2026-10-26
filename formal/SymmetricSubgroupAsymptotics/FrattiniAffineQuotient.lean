import SymmetricSubgroupAsymptotics.PrimeFrattiniAutomorphismAction
import SymmetricSubgroupAsymptotics.SemidirectQuotientKernelCardinality

/-! The actual whole affine map on the original Frattini quotient.
Its kernel is bounded from the SAME original generating lifts. Every
subgroup keeps its actual image; no splitting of that subgroup and no
commutativity of the original translation group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FrattiniAffineQuotient

variable (p : ℕ) [Fact p.Prime] (N : Type*) [Group N] [Finite N]
    {C : Type*} [Group C] (φ : C →* MulAut N)

def action : C →* MulAut (Multiplicative (PrimeAbelianization p N)) :=
  (PrimeFrattiniAutomorphismAction.groupAction p N).comp φ

theorem compatible (c : C) :
    (primeAbelianizationGroupMap p N).comp (φ c).toMonoidHom=
      (action p N φ c).toMonoidHom.comp (primeAbelianizationGroupMap p N) := by
  apply MonoidHom.ext
  intro n
  exact (PrimeFrattiniAutomorphismAction.groupAction_apply p N (φ c) n).symm

def quotientHom : N ⋊[φ] C →*
    Multiplicative (PrimeAbelianization p N) ⋊[
      MonoidHom.id (MulAut (Multiplicative (PrimeAbelianization p N)))]
        MulAut (Multiplicative (PrimeAbelianization p N)) :=
  SemidirectQuotientKernelCardinality.quotientHom φ
    (MonoidHom.id _) (primeAbelianizationGroupMap p N) (action p N φ)
    (compatible p N φ)

theorem action_kernel_card_le (hN : IsPGroup p N) (hφ : Function.Injective φ) :
    Nat.card (action p N φ).ker≤(Nat.card (frattini N))^
      Module.finrank (ZMod p) (PrimeCharacters p N) := by
  letI : Finite (MulAut N) := Finite.of_injective
    (fun a : MulAut N => (a : N → N)) DFunLike.coe_injective
  let f : (action p N φ).ker →
      (PrimeFrattiniAutomorphismAction.groupAction p N).ker :=
    fun c => ⟨φ c.val,c.property⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    apply hφ
    exact congrArg (fun a : (PrimeFrattiniAutomorphismAction.groupAction p N).ker => a.val) he
  exact (Nat.card_le_card_of_injective f hf).trans
    (PrimeFrattiniAutomorphismAction.kernel_card_le_frattini_pow_primeRank p N hN)

theorem kernel_factor_card_le (hN : IsPGroup p N) (hφ : Function.Injective φ) :
    Nat.card (primeAbelianizationGroupMap p N).ker*Nat.card (action p N φ).ker≤
      (Nat.card (frattini N))^(Module.finrank (ZMod p) (PrimeCharacters p N)+1) := by
  rw [primeAbelianizationGroupMap_ker p N hN]
  calc
    Nat.card (frattini N)*Nat.card (action p N φ).ker≤
        Nat.card (frattini N)*(Nat.card (frattini N))^
          Module.finrank (ZMod p) (PrimeCharacters p N) :=
      Nat.mul_le_mul_left _ (action_kernel_card_le p N φ hN hφ)
    _=(Nat.card (frattini N))^(Module.finrank (ZMod p) (PrimeCharacters p N)+1) :=
      (pow_succ' _ _).symm

theorem kernel_card_le (hN : IsPGroup p N) (hφ : Function.Injective φ) :
    Nat.card (quotientHom p N φ).ker≤
      (Nat.card (frattini N))^(Module.finrank (ZMod p) (PrimeCharacters p N)+1) := by
  exact (SemidirectQuotientKernelCardinality.kernel_card φ
    (MonoidHom.id _) (primeAbelianizationGroupMap p N) (action p N φ)
    (compatible p N φ)).le.trans (kernel_factor_card_le p N φ hN hφ)

theorem subgroup_class_card_le [Finite C]
    (hN : IsPGroup p N) (hφ : Function.Injective φ)
    (H : Subgroup (N ⋊[φ] C)) :
    Nat.card (ConjClasses H)≤
      (Nat.card (frattini N))^(Module.finrank (ZMod p) (PrimeCharacters p N)+1)*
        Nat.card (ConjClasses (((quotientHom p N φ).comp H.subtype).range)) := by
  exact (SemidirectQuotientKernelCardinality.subgroup_class_card_le_kernel_mul_range φ
    (MonoidHom.id _) (primeAbelianizationGroupMap p N) (action p N φ)
    (compatible p N φ) H).trans
      (Nat.mul_le_mul_right _ (kernel_factor_card_le p N φ hN hφ))

end SymmetricSubgroupAsymptotics.FrattiniAffineQuotient
