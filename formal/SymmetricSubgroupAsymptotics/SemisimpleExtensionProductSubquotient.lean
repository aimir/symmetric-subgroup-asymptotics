import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Prod

/-! An actual semisimple target extension is a subquotient of a common
product. The source of its kernel quotient need not be semisimple. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem semisimple_extension_product_subquotient
    {R A E M N : Type} [Ring R]
    [AddCommGroup A] [Module R A] [IsSemisimpleModule R A]
    [AddCommGroup E] [Module R E]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (K : Submodule R A)
    (q : E →ₗ[R] K) (hq : Function.Surjective q)
    (i : E →ₗ[R] M) (hi : Function.Injective i)
    (j : (A ⧸ K) →ₗ[R] N) (hj : Function.Injective j) :
    ∃ (f : (E × (A ⧸ K)) →ₗ[R] M × N)
      (g : (E × (A ⧸ K)) →ₗ[R] A),
      Function.Injective f ∧ Function.Surjective g := by
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property K.mkQ
    K.mkQ_surjective (LinearMap.id : (A ⧸ K) →ₗ[R] (A ⧸ K))
  let f : (E × (A ⧸ K)) →ₗ[R] M × N := i.prodMap j
  let g : (E × (A ⧸ K)) →ₗ[R] A := (K.subtype.comp q).coprod s
  refine ⟨f, g, ?_, ?_⟩
  · intro x y hxy
    apply Prod.ext
    · exact hi (congrArg Prod.fst hxy)
    · exact hj (congrArg Prod.snd hxy)
  · intro x
    have hsection : K.mkQ (s (K.mkQ x)) = K.mkQ x :=
      LinearMap.congr_fun hs (K.mkQ x)
    have hmem : x - s (K.mkQ x) ∈ K := by
      apply (Submodule.Quotient.mk_eq_zero K).mp
      change K.mkQ (x - s (K.mkQ x)) = 0
      rw [map_sub, hsection, sub_self]
    obtain ⟨e, he⟩ := hq ⟨x - s (K.mkQ x), hmem⟩
    refine ⟨(e, K.mkQ x), ?_⟩
    change (q e : A) + s (K.mkQ x) = x
    rw [he]
    exact sub_add_cancel _ _

end SymmetricSubgroupAsymptotics

end
