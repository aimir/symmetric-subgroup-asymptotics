import SymmetricSubgroupAsymptotics.OriginalKernelCubicImageGeneration
import SymmetricSubgroupAsymptotics.PrimeSocleElementaryChart
import SymmetricSubgroupAsymptotics.ElementaryNormalModuleGenerators

/-! The actual selected binary socle consumes the original intersection
and image projector bounds. Its cubic restriction is the subgroup of
powers of the SAME actual original element. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SelectedBinarySocleCubicIntersection
open OriginalKernelModuleChart
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem normalGen_le_two {Q B : Type} [Group Q] [Finite Q] [Group B]
    (pi : Q →* B) :
    let C := selectedPrimeSoclePartElementaryChart 2 (G := Q) (fun _ => True)
    let E := C.originalKernelChart
    ∀ (g : Q), g^3=1 → g≠1 →
      Module.finrank (ZMod 2) (LinearMap.range
        (1+(E.kernelIntersection pi).toRepresentation g+
          ((E.kernelIntersection pi).toRepresentation g)^2))≤2 →
      Module.finrank (ZMod 2) (LinearMap.range
        ((E.kernelIntersection pi).toRepresentation g+
          ((E.kernelIntersection pi).toRepresentation g)^2))≤2 →
      Nat.card (E.elementaryImageHom pi).range≤4 →
      (∀ x∈(E.elementaryImageHom pi).range, pi g*x*(pi g)⁻¹=x → x=1) →
      MarkedC4.normalGen (minimalNormalSoclePart Q (fun M => IsPGroup 2 M))≤2 := by
  intro C E g hg hgn hke hkf hcard hfix
  letI : FiniteDimensional (ZMod 2) C.quotientRepresentation := C.finiteDimensional
  letI : Finite C.quotientRepresentation := Module.finite_of_finite (ZMod 2)
  let H := Subgroup.zpowers g
  let a : H := ⟨g,Subgroup.mem_zpowers g⟩
  have hH : Nat.card H=3 := by
    rw [Nat.card_zpowers,orderOf_eq_prime hg hgn]
  letI : NeZero (Nat.card H : ZMod 2) := ⟨by rw [hH]; decide⟩
  have ha : a^3=1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow,Subgroup.coe_one] using hg
  have hgen : ∀ h : H, ∃ n : ℕ, h=a^n := by
    intro h
    have hm : (h : Q)∈Submonoid.powers g := mem_powers_iff_mem_zpowers.mpr h.property
    obtain ⟨n,hn⟩ := hm
    exact ⟨n,Subtype.ext hn.symm⟩
  have hgenerated : RepresentationGeneratedBy C.quotientRepresentation.ρ 2 :=
    E.generatedBy_two_of_cubic_intersection pi H.subtype a hgen ha hke hkf hcard hfix
  have hn := normalGen_le_of_elementaryQuotientRepresentation_generated
    (minimalNormalSoclePart Q (fun M => True ∧ IsPGroup 2 M)) C 2 hgenerated
  simpa only [true_and] using hn

end SymmetricSubgroupAsymptotics.SelectedBinarySocleCubicIntersection
