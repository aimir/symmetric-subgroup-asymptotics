import SymmetricSubgroupAsymptotics.PermutationWreathColoredConjugacy
import Mathlib.Data.Finite.Card

/-! Actual conjugacy classes inject into positive colored parts of the
actual point-set size. Representatives are chosen only to define a map;
injectivity uses the constructed colored-data conjugator. No converse
invariance or conjugacy-class count is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.PermutationWreathClassData
open PermutationCycleDecomposition PermutationWreathColoredConjugacy
  PermutationWreathBaseConjugacy

abbrev ColoredParts (D : Type*) (n : ℕ) :=
  {s : Multiset (ℕ × D) // (∀t∈s,0<t.1) ∧ (s.map Prod.fst).sum=n}

variable {D I : Type*} [CommGroup D] [Finite I]

theorem cycleLength_sum (σ : Equiv.Perm I) [Fintype (CycleIndex σ)] :
    (∑c,cycleLength σ c)=Nat.card I := by
  calc
    (∑c,cycleLength σ c)=∑c,Nat.card (Fin (cycleLength σ c)) := by simp only [Nat.card_fin]
    _=Nat.card (Σc : CycleIndex σ,Fin (cycleLength σ c)) := Nat.card_sigma.symm
    _=Nat.card I := Nat.card_congr (pointChart σ)

theorem coloredData_positive (σ : Equiv.Perm I) (f : I → D)
    (t : ℕ × D) (ht : t∈coloredData σ f) : 0<t.1 := by
  letI : Fintype (CycleIndex σ) := Fintype.ofFinite _
  change t∈Finset.univ.val.map (cycleLabels σ f) at ht
  obtain ⟨c,_,rfl⟩ := Multiset.mem_map.mp ht
  exact cycleLength_pos σ c

theorem coloredData_sum (σ : Equiv.Perm I) (f : I → D) :
    ((coloredData σ f).map Prod.fst).sum=Nat.card I := by
  letI : Fintype (CycleIndex σ) := Fintype.ofFinite _
  change ((Finset.univ.val.map (cycleLabels σ f)).map Prod.fst).sum=Nat.card I
  rw [Multiset.map_map]
  change (∑c,cycleLength σ c)=Nat.card I
  exact cycleLength_sum σ

def classRepresentative (c : ConjClasses (Wreath D I)) : Wreath D I :=
  Classical.choose (ConjClasses.exists_rep c)

omit [Finite I] in
theorem mk_classRepresentative (c : ConjClasses (Wreath D I)) :
    ConjClasses.mk (classRepresentative c)=c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

def classColoredData (c : ConjClasses (Wreath D I)) : Multiset (ℕ × D) :=
  wreathColoredData (classRepresentative c)

theorem classColoredData_injective : Function.Injective
    (classColoredData : ConjClasses (Wreath D I) → Multiset (ℕ × D)) := by
  intro c d he
  have hc := wreathColoredData_eq_isConj (classRepresentative c) (classRepresentative d) he
  have hm := ConjClasses.mk_eq_mk_iff_isConj.mpr hc
  simpa only [mk_classRepresentative] using hm

def classDataMap : ConjClasses (Wreath D I) → ColoredParts D (Nat.card I) :=
  fun c => ⟨classColoredData c,by
    constructor
    · exact coloredData_positive _ _
    · exact coloredData_sum _ _⟩

theorem classDataMap_injective : Function.Injective
    (classDataMap : ConjClasses (Wreath D I) → ColoredParts D (Nat.card I)) := by
  intro c d he
  exact classColoredData_injective (congrArg Subtype.val he)

end SymmetricSubgroupAsymptotics.PermutationWreathClassData
