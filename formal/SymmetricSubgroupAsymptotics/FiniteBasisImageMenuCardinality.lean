import SymmetricSubgroupAsymptotics.FiniteLinearActionOrderBound

/-! A finite menu of possible basis images counts actual linear maps.
The coefficient ring may be the integers; no finite ambient module or
field order is required. This supplies a small Weyl-word menu whenever
the actual integral basis is sent into the finite original root set. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteBasisImageMenuCardinality

theorem card_le_of_basis_image_menu {R M T I A : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [Finite I] [Finite A]
    (b : Module.Basis I R M) (root : A → M) (rho : T → (M →ₗ[R] M))
    (hinj : Function.Injective rho) (hroot : ∀ g i, ∃ a, root a=rho g (b i)) :
    Nat.card T ≤ (Nat.card A)^(Nat.card I) := by
  let encode : T → (I → A) := fun g i => Classical.choose (hroot g i)
  have he : Function.Injective encode := by
    intro g h hgh
    apply hinj
    apply b.ext
    intro i
    calc
      rho g (b i)=root (encode g i) := (Classical.choose_spec (hroot g i)).symm
      _=root (encode h i) := congrArg root (congrFun hgh i)
      _=rho h (b i) := Classical.choose_spec (hroot h i)
  exact (Nat.card_le_card_of_injective encode he).trans_eq Nat.card_fun

end SymmetricSubgroupAsymptotics.FiniteBasisImageMenuCardinality
