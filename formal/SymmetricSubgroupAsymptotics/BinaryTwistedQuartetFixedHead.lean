import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetTrivialHead

/-! Fixed-type sections have at most two binary coordinates even when
the entire retained section is not fixed. Averaging is over the actual
order-three operator only. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTwistedQuartetFixedHead
open BinaryTwistedQuartetPolynomial (Bit)
open BinaryTwistedQuartetLoewyCoordinates

theorem fixed_rank_le_two (W : Submodule Bit Space)
    (hcycle : ∀ v, v∈W → cycleAction v∈W)
    {Q : Type} [AddCommGroup Q] [Module Bit Q]
    (q : W →ₗ[Bit] Q) (hq : Function.Surjective q) (T : Module.End Bit Q)
    (hT : T^3=1)
    (hinter : ∀ v : W, q ⟨cycleAction v,hcycle v v.property⟩=T (q v)) :
    Module.finrank Bit (LinearMap.range (1+T+T^2))≤2 := by
  let P : Module.End Bit Q := 1+T+T^2
  have hPT : P*T=P := by
    change (1+T+T^2)*T=1+T+T^2
    rw [add_mul,add_mul,one_mul,← pow_two,← pow_succ,hT]
    abel
  let f : W →ₗ[Bit] P.range := P.rangeRestrict.comp q
  have hf : Function.Surjective f := P.surjective_rangeRestrict.comp hq
  apply BinaryTwistedQuartetTrivialHead.rank_le_two W hcycle f hf
  intro v
  apply Subtype.ext
  change P (q ⟨cycleAction v,hcycle v v.property⟩)=P (q v)
  rw [hinter]
  exact congrArg (fun u : Module.End Bit Q => u (q v)) hPT

end SymmetricSubgroupAsymptotics.BinaryTwistedQuartetFixedHead
