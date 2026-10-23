import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A faithful finite-field linear action is bounded by its actual
basis-image tuples. No group order formula or chosen natural-model
identification is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteLinearActionOrderBound
variable (F V : Type*) [Field F] [Finite F] [AddCommGroup V] [Module F V] [Finite V]

theorem card_le_pow_finrank_square {G : Type*} [Group G]
    (rho : G→*(V≃ₗ[F]V)) (hinj : Function.Injective rho) :
    Nat.card G≤Nat.card F^(Module.finrank F V)^2 := by
  let b := Module.finBasis F V
  let encode : G→(Fin (Module.finrank F V)→V) := fun g i=>rho g (b i)
  have he : Function.Injective encode := by
    intro g h hgh
    apply hinj
    apply b.ext'
    intro i
    exact congrFun hgh i
  calc
    Nat.card G≤Nat.card (Fin (Module.finrank F V)→V) :=
      Nat.card_le_card_of_injective encode he
    _ =Nat.card F^(Module.finrank F V)^2 := by
      rw [Nat.card_fun,Nat.card_fin,Module.natCard_eq_pow_finrank (K:=F) (V:=V),
        ←pow_mul,pow_two]

end SymmetricSubgroupAsymptotics.FiniteLinearActionOrderBound
