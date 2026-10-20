import SymmetricSubgroupAsymptotics.CoprimeSemidirectSubgroupRetraction
import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Original quotient bounds from literal generator lifts into a coprime
affine group. The lifted subgroup must contain the displayed complement;
its translation space is recovered by the generic retraction theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace SplitAffineLiteralSocles

open SemidirectProduct LinearSemidirectCoprimeSocleBounds

variable {p n : ℕ} [Fact p.Prime]
  {H V G : Type} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod p) V]
  [FiniteDimensional (ZMod p) V] [Group G]

/-- Literal equality of a lifted tuple identifies its image with the
original top. Every original normal quotient receives the inherited bound. -/
theorem quotientSocle
    (rho : H →* (V ≃ₗ[ZMod p] V)) (action : Model rho →* G)
    (lifted : Fin n → Model rho) (target : Fin n → G)
    (index : Equiv.Perm (Fin n))
    (hbinding : ∀ i, action (lifted i) = target (index i))
    (hH : ∀ h : H, (inr h : Model rho) ∈ Subgroup.closure (Set.range lifted))
    (hcop : Nat.Coprime p (Nat.card H)) (t a : ℕ)
    (hgen : RepresentationGeneratedBy (linearRepresentation rho) t)
    (hquotient : ∀ L : Subgroup H, L.Normal → MarkedC4.normalGen L ≤ a)
    (N : Subgroup (Subgroup.closure (Set.range target))) [N.Normal] :
    SocleNormalGeneratorBound (Subgroup.closure (Set.range target) ⧸ N) (max t a) := by
  let K := Subgroup.closure (Set.range lifted)
  let f : K →* G := action.comp K.subtype
  have hf (i : Fin n) : f (closureGenerators lifted i) = target (index i) :=
    hbinding i
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) target index
    (closureGenerators_full lifted) hf
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) target index
      (closureGenerators_full lifted) hf
  exact CoprimeSemidirectSubgroupRetraction.socle_of_surjective rho K hH
    hcop t a hgen hquotient ((QuotientGroup.mk' N).comp pi)
      ((QuotientGroup.mk'_surjective N).comp hpi)

end SplitAffineLiteralSocles
end SymmetricSubgroupAsymptotics

end
