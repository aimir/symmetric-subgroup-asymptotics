import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupsOfGenerators
import SymmetricSubgroupAsymptotics.CFSGReeFFourBorelOvergroupExtraction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicFlag

/-! The two literal relative parabolics are exactly the minimal strict
overgroups of the actual positive normalizer in the original fixed
group. Separation is supplied by the two proved integer flags, and
exhaustion by actual fixed-Bruhat/simple-seed extraction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMinimalParabolics
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourBorelOvergroupExtraction
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourMiddleParabolicFlag
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourOriginalWeylWords CFSGReeFFourFixedWordClassification
open CFSGReeFFourPairedWordActions CFSGReeFFourRelativeWeylRawWords
open CFSGMinimalOvergroupsOfGenerators

def simpleWeyl (m : ℕ) (middle : Bool) : originalModelFixed m := fixedPairedWord m [middle]

theorem simpleWeyl_false (m : ℕ) : simpleWeyl m false=outerFixedWeyl m := by
  apply Subtype.ext
  simp only [simpleWeyl,fixedPairedWord,expandPaired,pairedRelativeWord,Bool.false_eq_true,
    ite_false,List.append_nil,modelWeylWord,mul_one,outerFixedWeyl,outerRelativeWeyl]

theorem simpleWeyl_true (m : ℕ) : simpleWeyl m true=middleFixedWeyl m := by
  apply Subtype.ext
  simp only [simpleWeyl,fixedPairedWord,expandPaired,pairedRelativeWord,ite_true,
    List.append_nil,modelWeylWord,mul_one,middleFixedWeyl,middleRelativeWeyl,mul_assoc]

def simpleParabolic (m : ℕ) (middle : Bool) : Subgroup (originalModelFixed m) :=
  generatorOvergroup (fixedBorel m) (simpleWeyl m) middle

theorem simpleParabolic_false (m : ℕ) : simpleParabolic m false=outerParabolic m := by
  rw [simpleParabolic,generatorOvergroup,simpleWeyl_false,fixedBorel_eq_sup]
  rfl

theorem simpleParabolic_true (m : ℕ) : simpleParabolic m true=middleParabolic m := by
  rw [simpleParabolic,generatorOvergroup,simpleWeyl_true,fixedBorel_eq_sup]
  rfl

theorem other_simple_not_mem_parabolic (m : ℕ) (i j : Bool) (hne : j≠i) :
    simpleWeyl m j∉simpleParabolic m i := by
  cases i <;> cases j
  · exact False.elim (hne rfl)
  · rw [simpleWeyl_true,simpleParabolic_false]
    exact middleFixedWeyl_not_mem_outerParabolic m
  · rw [simpleWeyl_false,simpleParabolic_true]
    intro hw
    have hflag := middleParabolic_le_flag m hw
    change CFSGFFourOriginalMiddleWords.rawHom (Field m) (outerRelativeWeyl m)∈
      middleFlag (Field m) at hflag
    rw [rawHom_outerRelativeWeyl] at hflag
    exact outer_word_not_mem_flag (Field m) hflag
  · exact False.elim (hne rfl)

private theorem simpleWeyl_not_mem_borel (m : ℕ) (i : Bool) :
    simpleWeyl m i∉fixedBorel m := by
  intro hi
  cases i
  · exact other_simple_not_mem_parabolic m true false (by decide)
      ((show fixedBorel m≤simpleParabolic m true from le_sup_left) hi)
  · exact other_simple_not_mem_parabolic m false true (by decide)
      ((show fixedBorel m≤simpleParabolic m false from le_sup_left) hi)

theorem borel_lt_simpleParabolic (m : ℕ) (i : Bool) : fixedBorel m<simpleParabolic m i :=
  base_lt_generatorOvergroup (fixedBorel m) (simpleWeyl m) (simpleWeyl_not_mem_borel m) i

theorem simpleParabolic_minimal (m : ℕ) (i : Bool) (H : Subgroup (originalModelFixed m))
    (hBH : fixedBorel m<H) (hHP : H≤simpleParabolic m i) : H=simpleParabolic m i :=
  generatorOvergroup_minimal (fixedBorel m) (simpleWeyl m)
    (other_simple_not_mem_parabolic m) (exists_simple_relative_weyl_mem_of_borel_lt m) i H hBH hHP

theorem minimal_overgroup_eq_simpleParabolic (m : ℕ) (H : Subgroup (originalModelFixed m))
    (hBH : fixedBorel m<H)
    (hmin : ∀M : Subgroup (originalModelFixed m),fixedBorel m<M→M≤H→M=H) :
    ∃i : Bool,H=simpleParabolic m i :=
  minimal_overgroup_eq_generatorOvergroup (fixedBorel m) (simpleWeyl m)
    (simpleWeyl_not_mem_borel m) (exists_simple_relative_weyl_mem_of_borel_lt m) H hBH hmin

theorem simpleParabolic_injective (m : ℕ) : Function.Injective (simpleParabolic m) :=
  generatorOvergroup_injective (fixedBorel m) (simpleWeyl m) (other_simple_not_mem_parabolic m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMinimalParabolics
