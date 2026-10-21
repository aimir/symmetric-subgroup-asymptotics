import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangularSylow
import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangularNormalizer
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularSoluble
import SymmetricSubgroupAsymptotics.CFSGTypeAUpperOppositeGeneration
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Actual good defining-characteristic Sylow data for every literal
PSL_n over a finite field, n≥2. The unitriangular Sylow, its original
soluble normalizer, and the signed-reversal conjugating element are all
constructed in the same matrix group before taking its actual center
quotient. There is no remaining normalizer/order/generation premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAGoodSylow
open CFSGUpperUnitriangular CFSGReduction

def actualUpperSylow (F : Type*) [Field F] [Finite F] (p n : ℕ)
    [Fact p.Prime] [CharP F p] : Sylow p (SL F n) :=
  sylowOfBorelNormalizer F p n (normalizer_upperUnitriangular_le_borel F n)

@[simp] theorem actualUpperSylow_coe (F : Type*) [Field F] [Finite F] (p n : ℕ)
    [Fact p.Prime] [CharP F p] :
    (actualUpperSylow F p n : Subgroup (SL F n))=upperUnitriangular F n := rfl

theorem actualUpperSylow_normalizer_soluble (F : Type*) [Field F] [Finite F]
    (p n : ℕ) [Fact p.Prime] [CharP F p] :
    IsSolvable (Subgroup.normalizer (actualUpperSylow F p n : Set (SL F n))) := by
  letI : IsSolvable (borel F n) := borel_soluble F n
  exact solvable_of_solvable_injective
    (f := Subgroup.inclusion (normalizer_upperUnitriangular_le_borel F n))
    (Subgroup.inclusion_injective _)

theorem sl_goodSylowPrime (F : Type*) [Field F] [Finite F]
    (p n : ℕ) [Fact p.Prime] [CharP F p] (hn : 2 ≤ n) :
    GoodSylowPrime (SL F n) p := by
  refine ⟨Fact.out,actualUpperSylow F p n,
    CFSGTypeAUpperOppositeGeneration.reversingLift F n hn,?_,?_⟩
  · exact actualUpperSylow_normalizer_soluble F p n
  · exact CFSGTypeAUpperOppositeGeneration.upper_opposite_generate F n hn

theorem psl_goodSylowPrime (F : Type*) [Field F] [Finite F]
    (p n : ℕ) [Fact p.Prime] [CharP F p] (hn : 2 ≤ n) :
    GoodSylowPrime (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p := by
  let q := QuotientGroup.mk' (Subgroup.center (SL F n))
  exact goodSylowPrime_surjective q (QuotientGroup.mk'_surjective _)
    (sl_goodSylowPrime F p n hn)

end SymmetricSubgroupAsymptotics.CFSGTypeAGoodSylow
