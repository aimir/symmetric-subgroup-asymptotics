import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity
import SymmetricSubgroupAsymptotics.InducedTernaryWidthGenerators

/-!
# Sharp ternary generators in an actual wreath affine kernel

The literal correlated elementary kernel embeds in the induced module at
one actual block.  In local characteristic three and local dimension one,
the canonical ternary Sylow width therefore bounds the number of generators
of every invariant subspace of the actual correlated kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace ActualWreathAffineCapacity

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
  [MulAction Q I] [FaithfulSMul Q I]

variable (S : ActualWreathCompressionState Q I)
  {D' : Type} [Group D'] [Finite D']
  (phi : S.D →* D') (hphi : Function.Surjective phi)
  (C : ElementaryMinimalNormalChart phi.ker)

/-- Sharp generator bound on the actual correlated elementary kernel.  It
is obtained on the literal induced module and then pulled back through the
injective block-evaluation intertwiner. -/
theorem ambientTernary_uniformSubrepresentationGeneratorBound
    (hp : C.p = 3)
    (hdim : Module.finrank (ZMod C.p) C.V = 1)
    (i₀ : I) :
    UniformSubrepresentationGeneratorBound
      (ambientRepresentation S phi C)
      (ternaryWidthCore (Fintype.card I)
        ((Fintype.card I).factorization 3)) := by
  rcases C with ⟨p, hpprime, V, equiv⟩
  dsimp only at hp hdim
  subst p
  let C : ElementaryMinimalNormalChart phi.ker :=
    { p := 3
      p_prime := hpprime
      V := V
      equiv := equiv }
  change Module.finrank (ZMod 3) C.V = 1 at hdim
  have hind := inducedTernary_uniformSubrepresentationGeneratorBound
    (S.topPointStabilizer i₀) (localRepresentation S phi C i₀)
  change UniformSubrepresentationGeneratorBound
    (Representation.ind (S.topPointStabilizer i₀).subtype
      (localRepresentation S phi C i₀))
    (Module.finrank (ZMod 3) C.V *
      ternaryWidthCore (S.topPointStabilizer i₀).index
        ((S.topPointStabilizer i₀).index.factorization 3)) at hind
  have hambient := UniformSubrepresentationGeneratorBound.of_injective hind
    (inducedIntertwiner S phi C i₀)
    (inducedIntertwiner_injective S phi C i₀)
  have hindex : (S.topPointStabilizer i₀).index = Fintype.card I :=
    S.topPointStabilizer_index i₀
  change UniformSubrepresentationGeneratorBound
    (ambientRepresentation S phi C)
    (ternaryWidthCore (Fintype.card I)
      ((Fintype.card I).factorization 3))
  simpa only [inducedRepresentation, hindex, hdim, one_mul] using hambient

end ActualWreathAffineCapacity
end SymmetricSubgroupAsymptotics

end
