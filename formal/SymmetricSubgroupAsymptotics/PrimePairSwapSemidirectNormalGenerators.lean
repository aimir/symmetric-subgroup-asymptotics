import SymmetricSubgroupAsymptotics.PrimePairWreathNormalGenerators

/-! A pure coordinate swap makes the two-coordinate prime module
uniformly cyclic, even when the ambient complement has additional scalar
or diagonal actions. This supplies the elementary-kernel position without
a module census or a coprimality hypothesis. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimePairSwapSemidirectNormalGenerators

open LinearSemidirectCoprimeSocleBounds

variable (p : ℕ) [Fact p.Prime]
  {R : Type} [Group R]
  (rho : R →* ((Fin 2 → ZMod p) ≃ₗ[ZMod p] (Fin 2 → ZMod p)))
  (swap : PrimePairWreathNormalGenerators.Binary →* R)
  (hswap : rho.comp swap = PrimePairWreathNormalGenerators.linearAction p)

include hswap in
theorem uniform : UniformSubrepresentationGeneratorBound (linearRepresentation rho) 1 := by
  apply UniformSubrepresentationGeneratorBound.of_comp (linearRepresentation rho) swap
  have he : (linearRepresentation rho).comp swap =
      linearRepresentation (PrimePairWreathNormalGenerators.linearAction p) := by
    apply MonoidHom.ext
    intro c
    have h := congrArg (fun f ↦ f c) hswap
    exact congrArg LinearEquiv.toLinearMap h
  rw [he]
  exact PrimePairWreathNormalGenerators.uniform p

include hswap in
theorem normalGen_le [Finite R] {a : ℕ}
    (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (Model rho)) [N.Normal] : MarkedC4.normalGen N ≤ 1 + a :=
  LinearSemidirectUniformNormalGenerators.normalGen_le rho 1 a
    (uniform p rho swap hswap) hR N

include hswap in
theorem normal_generating_tuples [Finite R] {a : ℕ}
    (hR : ∀ K : Subgroup R, K.Normal →
      ∃ x : Fin a → R, Subgroup.normalClosure (Set.range x) = K) :
    ∀ N : Subgroup (Model rho), N.Normal →
      ∃ x : Fin (1 + a) → Model rho, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  apply exists_normal_generating_tuple_of_normalGen_le N
  apply normalGen_le p rho swap hswap ?_ N
  intro K hK
  letI := hK
  obtain ⟨x, hx⟩ := hR K hK
  exact normalGen_le_of_fin_tuple x hx

end PrimePairSwapSemidirectNormalGenerators
end SymmetricSubgroupAsymptotics

end
