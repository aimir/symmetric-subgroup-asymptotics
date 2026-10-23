import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralLineAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedCover
import SymmetricSubgroupAsymptotics.CFSGTwistedA2NormSurjectivity
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! Every two nonzero actual central parameters are conjugate by an
actual endpoint-paired torus. The conjugator maps into the SAME original
derived fixed source and its ACTUAL centre quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGSerreOrdinaryTwists CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGTwistedA2UnipotentArrays

theorem exists_conjugate_centralFixed (q : CFSG.PrimePower) (s : ℕ)
    (b c : q.Extension 2) (hb : Condition q (s + 1) 0 b) (hc : Condition q (s + 1) 0 c)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    ∃ g : naturalFixed (s + 3) q,
      g * centralFixed q (s + 1) b hb * g⁻¹ = centralFixed q (s + 1) c hc := by
  have hbc : b ∈ centralParameters q (s + 1) := (centralCondition_iff q (s + 1) b).mp hb
  have hcc : c ∈ centralParameters q (s + 1) := (centralCondition_iff q (s + 1) c).mp hc
  have hratio : definingFieldAutomorphism q 2 (b⁻¹ * c) = b⁻¹ * c :=
    centralParameter_div_fixed q (s + 1) b hb0 hbc ⟨c, hcc⟩
  obtain ⟨a, ha⟩ := exists_norm_eq_fixed q (b⁻¹ * c) hratio
  have ha0 : a ≠ 0 := by
    intro he
    apply mul_ne_zero (inv_ne_zero hb0) hc0
    calc
      b⁻¹ * c = a * definingFieldAutomorphism q 2 a := ha.symm
      _ = 0 := by rw [he, zero_mul]
  have hab : a * definingFieldAutomorphism q 2 a * b = c := by
    rw [ha]
    field_simp [hb0]
  refine ⟨pairedTorus q s a, ?_⟩
  simpa only [hab] using pairedTorus_centralFixed_conjugation q s a b ha0 hb

def derivedRadicalHom (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q (s + 1) →* commutator (Fixed (s + 3) q) :=
  (originalDerivedCover q s).comp (fixedRadical q (s + 1)).subtype

def projectiveRadicalHom (q : CFSG.PrimePower) (s : ℕ) :
    fixedRadical q (s + 1) →* CFSG.Models.TwistedA (s + 3) q :=
  (QuotientGroup.mk' (Subgroup.center (commutator (Fixed (s + 3) q)))).comp (derivedRadicalHom q s)

def derivedCentralParameterHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (centralParameters q (s + 1)) →* commutator (Fixed (s + 3) q) :=
  (derivedRadicalHom q s).comp (centralRadicalHom q (s + 1))

def projectiveCentralParameterHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (centralParameters q (s + 1)) →* CFSG.Models.TwistedA (s + 3) q :=
  (projectiveRadicalHom q s).comp (centralRadicalHom q (s + 1))

theorem derivedCentralParameter_conjugate (q : CFSG.PrimePower) (s : ℕ)
    (x y : Multiplicative (centralParameters q (s + 1))) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : commutator (Fixed (s + 3) q),
      g * derivedCentralParameterHom q s x * g⁻¹ = derivedCentralParameterHom q s y := by
  have hx0 : x.toAdd.val ≠ 0 := by
    intro he
    apply hx
    apply Multiplicative.toAdd.injective
    exact Subtype.ext he
  have hy0 : y.toAdd.val ≠ 0 := by
    intro he
    apply hy
    apply Multiplicative.toAdd.injective
    exact Subtype.ext he
  obtain ⟨g, hg⟩ := exists_conjugate_centralFixed q s x.toAdd.val y.toAdd.val
    (centralParameters_condition q (s + 1) x.toAdd.val x.toAdd.property)
    (centralParameters_condition q (s + 1) y.toAdd.val y.toAdd.property) hx0 hy0
  refine ⟨originalDerivedCover q s g, ?_⟩
  change originalDerivedCover q s g *
    originalDerivedCover q s (centralFixed q (s + 1) x.toAdd.val
      (centralParameters_condition q (s + 1) x.toAdd.val x.toAdd.property)) *
      (originalDerivedCover q s g)⁻¹ =
    originalDerivedCover q s (centralFixed q (s + 1) y.toAdd.val
      (centralParameters_condition q (s + 1) y.toAdd.val y.toAdd.property))
  simpa only [map_mul, map_inv] using congrArg (originalDerivedCover q s) hg

theorem projectiveCentralParameter_conjugate (q : CFSG.PrimePower) (s : ℕ)
    (x y : Multiplicative (centralParameters q (s + 1))) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : CFSG.Models.TwistedA (s + 3) q,
      g * projectiveCentralParameterHom q s x * g⁻¹ = projectiveCentralParameterHom q s y := by
  obtain ⟨g, hg⟩ := derivedCentralParameter_conjugate q s x y hx hy
  let pi := QuotientGroup.mk' (Subgroup.center (commutator (Fixed (s + 3) q)))
  refine ⟨pi g, ?_⟩
  change pi g * pi (derivedCentralParameterHom q s x) * (pi g)⁻¹ =
    pi (derivedCentralParameterHom q s y)
  simpa only [map_mul, map_inv] using congrArg pi hg

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
