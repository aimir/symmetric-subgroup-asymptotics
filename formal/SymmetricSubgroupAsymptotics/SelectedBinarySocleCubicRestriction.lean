import SymmetricSubgroupAsymptotics.OriginalKernelCubicImageGeneration
import SymmetricSubgroupAsymptotics.PrimeSocleElementaryChart
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators

/-! The actual selected binary socle consumes the original intersection
and image projector bounds. Its cubic restriction is the subgroup of
powers of the SAME actual original element. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SelectedBinarySocleCubicRestriction
open OriginalKernelModuleChart
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem normalGen_le_two {Q B H : Type} [Group Q] [Finite Q] [Group B] [Group H] [Finite H]
    [NeZero (Nat.card H : ZMod 2)]
    (pi : Q →* B) :
    let C := selectedPrimeSoclePartElementaryChart 2 (G := Q) (fun _ => True)
    let E := C.originalKernelChart
    ∀ (f : H →* Q) (a : H), (∀ h : H, ∃ n : ℕ, h=a^n) → a^3=1 →
      Module.finrank (ZMod 2) (LinearMap.range
        (1+(E.kernelIntersection pi).toRepresentation (f a)+
          ((E.kernelIntersection pi).toRepresentation (f a))^2))≤2 →
      Module.finrank (ZMod 2) (LinearMap.range
        ((E.kernelIntersection pi).toRepresentation (f a)+
          ((E.kernelIntersection pi).toRepresentation (f a))^2))≤2 →
      Nat.card (E.elementaryImageHom pi).range≤4 →
      (∀ x∈(E.elementaryImageHom pi).range, pi (f a)*x*(pi (f a))⁻¹=x → x=1) →
      MarkedC4.normalGen (minimalNormalSoclePart Q (fun M => IsPGroup 2 M))≤2 := by
  intro C E f a hgen ha hke hkf hcard hfix
  letI : FiniteDimensional (ZMod 2) C.quotientRepresentation := C.finiteDimensional
  letI : Finite C.quotientRepresentation := Module.finite_of_finite (ZMod 2)
  have hgenerated : RepresentationGeneratedBy C.quotientRepresentation.ρ 2 :=
    E.generatedBy_two_of_cubic_intersection pi f a hgen ha hke hkf hcard hfix
  have hn := normalGen_le_of_elementaryQuotientRepresentation_generated
    (minimalNormalSoclePart Q (fun M => True ∧ IsPGroup 2 M)) C 2 hgenerated
  simpa only [true_and] using hn

end SymmetricSubgroupAsymptotics.SelectedBinarySocleCubicRestriction
