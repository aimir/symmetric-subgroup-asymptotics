import SymmetricSubgroupAsymptotics.G2PositiveDividedPowerWords
import SymmetricSubgroupAsymptotics.CFSGSerreSignedRootWeights
import SymmetricSubgroupAsymptotics.CFSGSerreFiniteRationalFirstActionSpan
import Mathlib.Tactic.FinCases

/-! Fourteen explicit ORIGINAL G2 rational source words span the original
Serre quotient. Every closure row follows from its OWN defining relations.
There is no native-image, source-simple or recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGG2OriginalRationalSourceSpan
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreSignedRootWeights
abbrev CM := CartanMatrix.G₂
abbrev Source := RationalLie CM

def a (neg : Bool) : Source := rootVector CM neg 0
def b (neg : Bool) : Source := rootVector CM neg 1

def v (neg : Bool) : Fin 6 → Source :=
  ![a neg,b neg,G2PositiveDividedPowerWords.c (a neg) (b neg),
    G2PositiveDividedPowerWords.d (a neg) (b neg),
    G2PositiveDividedPowerWords.e (a neg) (b neg),
    G2PositiveDividedPowerWords.f (a neg) (b neg)]

theorem first_serre (neg : Bool) : ⁅a neg,⁅a neg,⁅a neg,⁅a neg,b neg⁆⁆⁆⁆ = 0 := by
  cases neg with
  | false =>
      have h := generator_adE CM 0 1
      change (LieAlgebra.ad ℚ Source (a false)^4) (b false) = 0 at h
      simpa only [pow_succ',pow_zero,Module.End.mul_apply,Module.End.one_apply,
        LieAlgebra.ad_apply] using h
  | true =>
      have h := generator_adF CM 0 1
      change (LieAlgebra.ad ℚ Source (a true)^4) (b true) = 0 at h
      simpa only [pow_succ',pow_zero,Module.End.mul_apply,Module.End.one_apply,
        LieAlgebra.ad_apply] using h

theorem second_serre (neg : Bool) : ⁅b neg,⁅b neg,a neg⁆⁆ = 0 := by
  cases neg with
  | false =>
      have h := generator_adE CM 1 0
      change (LieAlgebra.ad ℚ Source (b false)^2) (a false) = 0 at h
      simpa only [pow_succ',pow_zero,Module.End.mul_apply,Module.End.one_apply,
        LieAlgebra.ad_apply] using h
  | true =>
      have h := generator_adF CM 1 0
      change (LieAlgebra.ad ℚ Source (b true)^2) (a true) = 0 at h
      simpa only [pow_succ',pow_zero,Module.End.mul_apply,Module.End.one_apply,
        LieAlgebra.ad_apply] using h

theorem lowering_rows (neg : Bool) :
    ⁅oppositeVector CM neg 0,v neg 2⁆ = (3:ℚ) • v neg 1 ∧
    ⁅oppositeVector CM neg 0,v neg 3⁆ = (2:ℚ) • v neg 2 ∧
    ⁅oppositeVector CM neg 0,v neg 4⁆ = v neg 3 ∧
    ⁅oppositeVector CM neg 0,v neg 5⁆ = 0 ∧
    ⁅oppositeVector CM neg 1,v neg 2⁆ = -v neg 0 ∧
    ⁅oppositeVector CM neg 1,v neg 3⁆ = 0 ∧
    ⁅oppositeVector CM neg 1,v neg 4⁆ = 0 ∧
    ⁅oppositeVector CM neg 1,v neg 5⁆ = v neg 4 := by
  apply G2PositiveDividedPowerWords.lowerings (a neg) (b neg)
    (oppositeVector CM neg 0) (oppositeVector CM neg 1)
    (coroot CM neg 0) (coroot CM neg 1)
  · exact opposite_same CM neg 0
  · exact opposite_distinct CM neg 0 1 (by decide)
  · exact opposite_distinct CM neg 1 0 (by decide)
  · exact opposite_same CM neg 1
  · have h := coroot_root CM neg 0 0
    change ⁅coroot CM neg 0,a neg⁆ = (2:ℚ) • a neg at h
    exact h
  · have h := coroot_root CM neg 0 1
    change ⁅coroot CM neg 0,b neg⁆ = (-3:ℚ) • b neg at h
    exact h
  · have h := coroot_root CM neg 1 0
    change ⁅coroot CM neg 1,a neg⁆ = (-1:ℚ) • a neg at h
    exact h
  · have h := coroot_root CM neg 1 1
    change ⁅coroot CM neg 1,b neg⁆ = (2:ℚ) • b neg at h
    exact h
  · exact second_serre neg

/-- Membership form retains the SAME chosen source submodule. -/
theorem raising_mem (S : Submodule ℚ Source) (neg : Bool)
    (hv : ∀ j, v neg j ∈ S) (i : Fin 2) (j : Fin 6) :
    ⁅rootVector CM neg i,v neg j⁆ ∈ S := by
  fin_cases i <;> fin_cases j
  · change ⁅a neg,a neg⁆ ∈ S
    rw [lie_self]
    exact S.zero_mem
  · change G2PositiveDividedPowerWords.c (a neg) (b neg) ∈ S
    exact hv 2
  · change ⁅a neg,G2PositiveDividedPowerWords.c (a neg) (b neg)⁆ ∈ S
    rw [G2PositiveDividedPowerWords.a_c]
    exact S.smul_mem 2 (hv 3)
  · change ⁅a neg,G2PositiveDividedPowerWords.d (a neg) (b neg)⁆ ∈ S
    rw [G2PositiveDividedPowerWords.a_d]
    exact S.smul_mem 3 (hv 4)
  · change ⁅a neg,G2PositiveDividedPowerWords.e (a neg) (b neg)⁆ ∈ S
    rw [G2PositiveDividedPowerWords.a_e _ _ (first_serre neg)]
    exact S.zero_mem
  · change ⁅a neg,G2PositiveDividedPowerWords.f (a neg) (b neg)⁆ ∈ S
    rw [G2PositiveDividedPowerWords.a_f _ _ (first_serre neg) (second_serre neg)]
    exact S.zero_mem
  · change ⁅b neg,a neg⁆ ∈ S
    rw [G2PositiveDividedPowerWords.b_a]
    exact S.neg_mem (hv 2)
  · change ⁅b neg,b neg⁆ ∈ S
    rw [lie_self]
    exact S.zero_mem
  · change ⁅b neg,G2PositiveDividedPowerWords.c (a neg) (b neg)⁆ ∈ S
    rw [G2PositiveDividedPowerWords.b_c _ _ (second_serre neg)]
    exact S.zero_mem
  · change ⁅b neg,G2PositiveDividedPowerWords.d (a neg) (b neg)⁆ ∈ S
    rw [G2PositiveDividedPowerWords.b_d _ _ (second_serre neg)]
    exact S.zero_mem
  · change G2PositiveDividedPowerWords.f (a neg) (b neg) ∈ S
    exact hv 5
  · change ⁅b neg,G2PositiveDividedPowerWords.f (a neg) (b neg)⁆ ∈ S
    rw [G2PositiveDividedPowerWords.b_f _ _ (second_serre neg)]
    exact S.zero_mem

theorem lowering_mem (S : Submodule ℚ Source) (neg : Bool)
    (hv : ∀ j, v neg j ∈ S) (hh : ∀ i, coroot CM neg i ∈ S)
    (i : Fin 2) (j : Fin 6) : ⁅oppositeVector CM neg i,v neg j⁆ ∈ S := by
  obtain ⟨hpc,hpd,hpe,hpf,hqc,hqd,hqe,hqf⟩ := lowering_rows neg
  fin_cases i <;> fin_cases j
  · change ⁅oppositeVector CM neg 0,rootVector CM neg 0⁆ ∈ S
    rw [opposite_same]
    exact S.neg_mem (hh 0)
  · change ⁅oppositeVector CM neg 0,rootVector CM neg 1⁆ ∈ S
    rw [opposite_distinct _ _ _ _ (by decide)]
    exact S.zero_mem
  · change ⁅oppositeVector CM neg 0,v neg 2⁆ ∈ S
    rw [hpc]
    exact S.smul_mem 3 (hv 1)
  · change ⁅oppositeVector CM neg 0,v neg 3⁆ ∈ S
    rw [hpd]
    exact S.smul_mem 2 (hv 2)
  · change ⁅oppositeVector CM neg 0,v neg 4⁆ ∈ S
    rw [hpe]
    exact hv 3
  · change ⁅oppositeVector CM neg 0,v neg 5⁆ ∈ S
    rw [hpf]
    exact S.zero_mem
  · change ⁅oppositeVector CM neg 1,rootVector CM neg 0⁆ ∈ S
    rw [opposite_distinct _ _ _ _ (by decide)]
    exact S.zero_mem
  · change ⁅oppositeVector CM neg 1,rootVector CM neg 1⁆ ∈ S
    rw [opposite_same]
    exact S.neg_mem (hh 1)
  · change ⁅oppositeVector CM neg 1,v neg 2⁆ ∈ S
    rw [hqc]
    exact S.neg_mem (hv 0)
  · change ⁅oppositeVector CM neg 1,v neg 3⁆ ∈ S
    rw [hqd]
    exact S.zero_mem
  · change ⁅oppositeVector CM neg 1,v neg 4⁆ ∈ S
    rw [hqe]
    exact S.zero_mem
  · change ⁅oppositeVector CM neg 1,v neg 5⁆ ∈ S
    rw [hqf]
    exact hv 4

def family : Fin 2 ⊕ (Bool × Fin 6) → Source
  | .inl i => generator CM (.H i)
  | .inr (neg,j) => v neg j

/-- Actual fourteen-word spanning of the ORIGINAL rational Serre source. -/
theorem span_eq_top : Submodule.span ℚ (Set.range family) = ⊤ := by
  let S := Submodule.span ℚ (Set.range family)
  have hv (neg : Bool) (j : Fin 6) : v neg j ∈ S :=
    Submodule.subset_span ⟨.inr (neg,j),rfl⟩
  have hh (neg : Bool) (i : Fin 2) : coroot CM neg i ∈ S := by
    have h : generator CM (.H i) ∈ S := Submodule.subset_span ⟨.inl i,rfl⟩
    cases neg
    · exact h
    · exact S.neg_mem h
  have hr (neg : Bool) (i : Fin 2) : rootVector CM neg i ∈ S := by
    fin_cases i
    · exact hv neg 0
    · exact hv neg 1
  apply CFSGSerreFiniteRationalFirstActionSpan.span_eq_top CM family
  · intro g
    cases g with
    | H i => exact Submodule.subset_span ⟨.inl i,rfl⟩
    | E i => exact hr false i
    | F i => exact hr true i
  · intro neg i j
    cases j with
    | inl k =>
        have h : ⁅rootVector CM neg i,coroot CM neg k⁆ ∈ S := by
          rw [← lie_skew (rootVector CM neg i) (coroot CM neg k),coroot_root]
          exact S.neg_mem (S.smul_mem _ (hr neg i))
        cases neg
        · exact h
        · have hn := S.neg_mem h
          simpa only [coroot,ite_true,lie_neg,neg_neg] using hn
    | inr w =>
        obtain ⟨which,j⟩ := w
        cases neg <;> cases which
        · exact raising_mem S false (hv false) i j
        · exact lowering_mem S true (hv true) (hh true) i j
        · exact lowering_mem S false (hv false) (hh false) i j
        · exact raising_mem S true (hv true) i j

end SymmetricSubgroupAsymptotics.CFSGG2OriginalRationalSourceSpan
