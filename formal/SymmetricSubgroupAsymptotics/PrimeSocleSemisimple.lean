import SymmetricSubgroupAsymptotics.PrimeSocleElementaryChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineFixedFrameRelativeHead
import SymmetricSubgroupAsymptotics.OriginalKernelQuotientChart
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Irreducible

/-!
# Semisimplicity of a selected prime-primary socle

A selected sum of ambient minimal normal elementary `p`-subgroups is a
semisimple module for the literal conjugation action of the ambient quotient.
The proof does not invoke Maschke: every selected minimal normal factor is a
simple submodule, and those literal factor submodules span the selected socle.

The inverse from invariant subspaces to ambient normal subgroups is the
original-kernel chart's `submoduleGroup`.  Thus simplicity follows directly
from ambient minimal normality and does not pass through an abstract
composition-series choice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type} [Group G] [Finite G]
variable (P : Subgroup G → Prop)

private abbrev SelectedPrimeSocle :=
  minimalNormalSoclePart G (fun M ↦ P M ∧ IsPGroup p M)

private abbrev SelectedPrimeChart :
    ElementaryMinimalNormalChart (SelectedPrimeSocle p P) :=
  selectedPrimeSoclePartElementaryChart p P

private abbrev SelectedPrimeRepresentation :=
  (SelectedPrimeChart p P).quotientRepresentation

private abbrev SelectedPrimeFactor :=
  {M : Subgroup G // IsMinimalNormalSubgroup M ∧ P M ∧ IsPGroup p M}

private def selectedPrimeFactorSubrepresentation
    (M : SelectedPrimeFactor p P) :
    Subrepresentation (SelectedPrimeRepresentation p P).ρ := by
  letI : M.1.Normal := M.2.1.1
  exact (SelectedPrimeChart p P).originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' (SelectedPrimeSocle p P))
    (QuotientGroup.mk'_surjective (SelectedPrimeSocle p P))
    (SelectedPrimeRepresentation p P) M.1

private theorem originalKernel_submoduleGroup_injective
    {k Q B : Type} [CommRing k] [Group Q] [Group B]
    (pi : Q →* B) (A : Rep k B)
    (C : OriginalKernelModuleChart pi A) :
    Function.Injective
      (OriginalKernelQuotientChart.submoduleGroup pi A C) := by
  intro K L hKL
  apply Submodule.ext
  intro v
  let a : Multiplicative A := Multiplicative.ofAdd v
  change a.toAdd ∈ K ↔ a.toAdd ∈ L
  rw [← OriginalKernelQuotientChart.chart_mem_submoduleGroup pi A C K a,
    hKL,
    OriginalKernelQuotientChart.chart_mem_submoduleGroup pi A C L a]

private theorem originalKernel_submoduleGroup_bot
    {k Q B : Type} [CommRing k] [Group Q] [Group B]
    (pi : Q →* B) (A : Rep k B)
    (C : OriginalKernelModuleChart pi A) :
    OriginalKernelQuotientChart.submoduleGroup pi A C
        (⊥ : Submodule k A) = ⊥ := by
  apply le_antisymm
  · intro g hg
    rcases hg with ⟨v, rfl⟩
    have hv0 : v = 1 := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact (show v.toAdd.1 = 0 from v.toAdd.2)
    subst v
    apply Subgroup.mem_bot.mpr
    exact map_one _
  · exact bot_le

private theorem originalKernel_submoduleGroup_mono
    {k Q B : Type} [CommRing k] [Group Q] [Group B]
    (pi : Q →* B) (A : Rep k B)
    (C : OriginalKernelModuleChart pi A) :
    Monotone (OriginalKernelQuotientChart.submoduleGroup pi A C) := by
  intro K L hKL g hg
  rcases hg with ⟨v, rfl⟩
  exact ⟨Multiplicative.ofAdd ⟨v.toAdd.1, hKL v.toAdd.2⟩, rfl⟩

private theorem selectedPrime_submoduleGroup_normal
    (T : Subrepresentation (SelectedPrimeRepresentation p P).ρ) :
    (OriginalKernelQuotientChart.submoduleGroup
      (QuotientGroup.mk' (SelectedPrimeSocle p P))
      (SelectedPrimeRepresentation p P)
      (SelectedPrimeChart p P).originalKernelChart T.toSubmodule).Normal := by
  apply OriginalKernelQuotientChart.submoduleGroup_normal
  intro b v hv
  exact T.apply_mem_toSubmodule b hv

private theorem selectedPrime_normalSubrepresentation_submoduleGroup
    (T : Subrepresentation (SelectedPrimeRepresentation p P).ρ) :
    let q := QuotientGroup.mk' (SelectedPrimeSocle p P)
    let C := SelectedPrimeChart p P
    let K := OriginalKernelQuotientChart.submoduleGroup
      q (SelectedPrimeRepresentation p P) C.originalKernelChart T.toSubmodule
    ∀ [K.Normal], C.originalKernelChart.normalSubrepresentation q
        (QuotientGroup.mk'_surjective (SelectedPrimeSocle p P))
        (SelectedPrimeRepresentation p P) K = T := by
  dsimp only
  intro _hK
  let E := SelectedPrimeSocle p P
  let C := SelectedPrimeChart p P
  let A := SelectedPrimeRepresentation p P
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let K := OriginalKernelQuotientChart.submoduleGroup
    q A C.originalKernelChart T.toSubmodule
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro v
  let e : E := C.equiv.symm (Multiplicative.ofAdd v)
  have hecoord : (C.equiv e).toAdd = v := by
    dsimp only [e]
    rw [C.equiv.apply_symm_apply]
    rfl
  have hintersection :
      (C.equiv e).toAdd ∈ C.originalKernelChart.normalSubrepresentation q
          (QuotientGroup.mk'_surjective E) A K ↔
        (e.1 : G) ∈ K := by
    exact elementaryIntersectionModule_mem_iff E C K e
  rw [← hecoord]
  change (C.equiv e).toAdd ∈
      C.originalKernelChart.normalSubrepresentation q
        (QuotientGroup.mk'_surjective E) A K ↔
    (C.equiv e).toAdd ∈ T
  have heoriginal :
      (C.originalKernelChart.equiv (C.equiv e) : G) = (e.1 : G) := by
    dsimp only [ElementaryMinimalNormalChart.originalKernelChart]
    calc
      ((C.quotientKernelEquiv (C.equiv e) :
          (QuotientGroup.mk' E).ker) : G) =
          (C.equiv.symm (C.equiv e) : E) :=
        C.quotientKernelEquiv_coe (C.equiv e)
      _ = (e.1 : G) := congrArg Subtype.val (C.equiv.symm_apply_apply e)
  rw [hintersection, ← heoriginal,
    OriginalKernelQuotientChart.chart_mem_submoduleGroup
      q A C.originalKernelChart T.toSubmodule (C.equiv e)]
  rfl

private theorem selectedPrimeFactor_submoduleGroup_eq
    (M : SelectedPrimeFactor p P) :
    let q := QuotientGroup.mk' (SelectedPrimeSocle p P)
    let C := SelectedPrimeChart p P
    OriginalKernelQuotientChart.submoduleGroup
      q (SelectedPrimeRepresentation p P) C.originalKernelChart
      (selectedPrimeFactorSubrepresentation p P M).toSubmodule = M.1 := by
  let E := SelectedPrimeSocle p P
  let C := SelectedPrimeChart p P
  let A := SelectedPrimeRepresentation p P
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let W := selectedPrimeFactorSubrepresentation p P M
  let K := OriginalKernelQuotientChart.submoduleGroup
    q A C.originalKernelChart W.toSubmodule
  letI : M.1.Normal := M.2.1.1
  letI : K.Normal := selectedPrime_submoduleGroup_normal p P W
  have hrep : C.originalKernelChart.normalSubrepresentation q
      (QuotientGroup.mk'_surjective E) A K = W :=
    selectedPrime_normalSubrepresentation_submoduleGroup p P W
  have hintersection : K.subgroupOf q.ker = M.1.subgroupOf q.ker :=
    (C.originalKernelChart.normalSubrepresentation_eq_iff_intersection_eq
      q (QuotientGroup.mk'_surjective E) A K M.1).1 hrep
  apply Subgroup.ext
  intro g
  have hKker : K ≤ q.ker :=
    OriginalKernelQuotientChart.submoduleGroup_le_kernel
      q A C.originalKernelChart W.toSubmodule
  have hMleE : M.1 ≤ E :=
    minimalNormal_le_minimalNormalSoclePart
      (fun L : Subgroup G ↦ P L ∧ IsPGroup p L) M.1 M.2.1 ⟨M.2.2.1, M.2.2.2⟩
  constructor
  · intro hg
    let kg : q.ker := ⟨g, hKker hg⟩
    have : kg ∈ K.subgroupOf q.ker := hg
    rw [hintersection] at this
    exact this
  · intro hg
    let kg : q.ker := ⟨g, by
      simpa only [q, QuotientGroup.ker_mk'] using hMleE hg⟩
    have hkg : kg ∈ M.1.subgroupOf q.ker := by
      exact hg
    rw [← hintersection] at hkg
    exact hkg

private theorem selectedPrimeFactor_isSimple
    (M : SelectedPrimeFactor p P) :
    IsSimpleModule (ZMod p)[G ⧸ SelectedPrimeSocle p P]
      (selectedPrimeFactorSubrepresentation p P M).asSubmodule := by
  let E := SelectedPrimeSocle p P
  let C := SelectedPrimeChart p P
  let A := SelectedPrimeRepresentation p P
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let W := selectedPrimeFactorSubrepresentation p P M
  rw [isSimpleModule_iff_isAtom, isAtom_iff_le_of_ge]
  constructor
  · intro hbot
    have hWbot : W.toSubmodule = (⊥ : Submodule (ZMod p) A) := by
      apply Submodule.ext
      intro v
      change v ∈ W.asSubmodule ↔ v ∈
        (⊥ : Submodule (ZMod p)[G ⧸ E] A.ρ.asModule)
      rw [hbot]
    have hgroup := congrArg
      (OriginalKernelQuotientChart.submoduleGroup q A C.originalKernelChart)
      hWbot
    have hMbot : M.1 = ⊥ := by
      rw [selectedPrimeFactor_submoduleGroup_eq p P M,
        originalKernel_submoduleGroup_bot] at hgroup
      exact hgroup
    exact M.2.1.2.1 hMbot
  · intro L hLbot hLW
    let T : Subrepresentation A.ρ := Subrepresentation.ofSubmodule' L
    let K := OriginalKernelQuotientChart.submoduleGroup
      q A C.originalKernelChart T.toSubmodule
    letI : K.Normal := selectedPrime_submoduleGroup_normal p P T
    have hKleM : K ≤ M.1 := by
      rw [← selectedPrimeFactor_submoduleGroup_eq p P M]
      apply originalKernel_submoduleGroup_mono q A C.originalKernelChart
      exact hLW
    have hKne : K ≠ ⊥ := by
      intro hKbot
      have hTbot : T.toSubmodule = (⊥ : Submodule (ZMod p) A) :=
        originalKernel_submoduleGroup_injective q A C.originalKernelChart
          (hKbot.trans
            (originalKernel_submoduleGroup_bot q A C.originalKernelChart).symm)
      apply hLbot
      apply Submodule.ext
      intro v
      change v ∈ T.toSubmodule ↔ v ∈ (⊥ : Submodule (ZMod p) A)
      rw [hTbot]
    have hKM : K = M.1 := M.2.1.2.2 K inferInstance hKne hKleM
    have hTW : T.toSubmodule = W.toSubmodule :=
      originalKernel_submoduleGroup_injective q A C.originalKernelChart
        (hKM.trans (selectedPrimeFactor_submoduleGroup_eq p P M).symm)
    intro v hv
    change v ∈ T.toSubmodule
    rw [hTW]
    exact hv

/-- The literal quotient-conjugation representation of every selected
prime-primary socle part is semisimple. -/
theorem selectedPrimeSoclePart_quotientRepresentation_isSemisimple :
    IsSemisimpleModule
      (ZMod p)[G ⧸ SelectedPrimeSocle p P]
      (SelectedPrimeRepresentation p P).ρ.asModule := by
  let E := SelectedPrimeSocle p P
  let C := SelectedPrimeChart p P
  let A := SelectedPrimeRepresentation p P
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  let factor := selectedPrimeFactorSubrepresentation p P
  have hsimple (M : SelectedPrimeFactor p P) :
      IsSemisimpleModule (ZMod p)[G ⧸ E] (factor M).asSubmodule := by
    letI : IsSimpleModule (ZMod p)[G ⧸ E] (factor M).asSubmodule := by
      simpa only [E, factor] using selectedPrimeFactor_isSimple p P M
    exact inferInstance
  apply isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun M : SelectedPrimeFactor p P ↦ (factor M).asSubmodule)
  · intro M
    exact hsimple M
  · apply top_unique
    intro v _hv
    let L : Submodule (ZMod p)[G ⧸ E] A.ρ.asModule :=
      sSup (Set.range (fun M : SelectedPrimeFactor p P ↦
        (factor M).asSubmodule))
    let T : Subrepresentation A.ρ := Subrepresentation.ofSubmodule' L
    let K := OriginalKernelQuotientChart.submoduleGroup
      q A C.originalKernelChart T.toSubmodule
    letI : K.Normal := selectedPrime_submoduleGroup_normal p P T
    have hEleK : E ≤ K := by
      apply minimalNormalSoclePart_le_of
      intro M hM hMP
      let m : SelectedPrimeFactor p P := ⟨M, hM, hMP.1, hMP.2⟩
      have hmgroup : OriginalKernelQuotientChart.submoduleGroup
          q A C.originalKernelChart (factor m).toSubmodule = m.1 := by
        simpa only [q, A, C, factor, E] using
          selectedPrimeFactor_submoduleGroup_eq p P m
      intro x hx
      have hxsource : x ∈ OriginalKernelQuotientChart.submoduleGroup
          q A C.originalKernelChart (factor m).toSubmodule := by
        rw [hmgroup]
        exact hx
      have hfactorT : (factor m).toSubmodule ≤ T.toSubmodule := by
        intro a ha
        change a ∈ L
        have hle : (factor m).asSubmodule ≤
            sSup (Set.range (fun M : SelectedPrimeFactor p P ↦
              (factor M).asSubmodule)) :=
          le_sSup (Set.mem_range_self m)
        exact hle ha
      exact originalKernel_submoduleGroup_mono q A C.originalKernelChart
        hfactorT hxsource
    let e : E := C.equiv.symm (Multiplicative.ofAdd v)
    have heK : (e.1 : G) ∈ K := hEleK e.2
    have hKT : C.originalKernelChart.normalSubrepresentation q
        (QuotientGroup.mk'_surjective E) A K = T :=
      selectedPrime_normalSubrepresentation_submoduleGroup p P T
    have heT : (C.equiv e).toAdd ∈ T := by
      rw [← hKT]
      exact (elementaryIntersectionModule_mem_iff E C K e).2 heK
    have hecoord : (C.equiv e).toAdd = v := by
      dsimp only [e]
      rw [C.equiv.apply_symm_apply]
      rfl
    rw [hecoord] at heT
    exact heT

end SymmetricSubgroupAsymptotics

end
