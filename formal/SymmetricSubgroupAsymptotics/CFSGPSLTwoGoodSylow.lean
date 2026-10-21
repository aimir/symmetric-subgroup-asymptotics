import SymmetricSubgroupAsymptotics.CFSGSLTwoUpperSylow
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrimeSurjective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Actual defining-characteristic good Sylow data for literal PSL₂.
The two conjugates are the images of opposite root groups, and the
normalizer is the image of the same soluble triangular normalizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGoodSylow
open Matrix CFSGTypeAElementaryMatrices CFSGTypeASLTwoWeyl
open CFSGSLTwoUpperRoots CFSGSLTwoUpperSylow CFSGReduction
variable {F : Type*} [Field F]

theorem opposite_roots_generate :
    Subgroup.closure ((upperRoot (F:=F) : Set (SL2 (F:=F))) ∪
      (upperRoot (F:=F)).map (MulAut.conj (weyl (F:=F))).toMonoidHom)=⊤ := by
  let K := Subgroup.closure ((upperRoot (F:=F) : Set (SL2 (F:=F))) ∪
    (upperRoot (F:=F)).map (MulAut.conj (weyl (F:=F))).toMonoidHom)
  have hu (a : F) : upper a∈K := Subgroup.subset_closure (Or.inl (upper_mem a))
  have hl (a : F) : lower a∈K := by
    apply Subgroup.subset_closure
    apply Or.inr
    refine ⟨upper (-a),upper_mem (-a),?_⟩
    change weyl*upper (-a)*weyl⁻¹=lower a
    rw [weyl_upper,neg_neg]
  apply CFSGTypeAElementaryGeneration.eq_top_of_elementary
  intro i j hij a
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hu a
  · exact hl a
  · exact (hij rfl).elim

theorem sl_goodSylowPrime [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    GoodSylowPrime (SL2 (F:=F)) p := by
  refine ⟨Fact.out,upperSylow (F:=F) (p:=p),weyl,?_,?_⟩
  · exact upperRoot_normalizer_isSolvable
  · exact opposite_roots_generate

theorem psl_goodSylowPrime [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    GoodSylowPrime (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) p := by
  let q := QuotientGroup.mk' (Subgroup.center (SL2 (F:=F)))
  exact goodSylowPrime_surjective q (QuotientGroup.mk'_surjective _)
    (sl_goodSylowPrime (F:=F) p)

/-- In particular every finite field of cardinality at least four has
the required actual good prime. The witness is its defining prime. -/
theorem exists_psl_goodSylowPrime [Finite F] :
    ∃ p,GoodSylowPrime (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) p := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p,hchar,n,hp,_hn⟩ := FiniteField.card' F
  letI : CharP F p := hchar
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨p,psl_goodSylowPrime p⟩

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGoodSylow
