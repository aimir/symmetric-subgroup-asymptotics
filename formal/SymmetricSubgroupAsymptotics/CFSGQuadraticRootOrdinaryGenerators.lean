import SymmetricSubgroupAsymptotics.FiniteHomFamilyOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimeFieldBasisOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootSubgroup

/-! Ordinary generators of the SAME canonical elementary matrix group.
Each signed simple-root parameter is an actual additive homomorphism;
a genuine prime-field basis supplies its finite parameter set. This
requires no simplicity, source faithfulness, or identification of the
original Serre model. An original-model consumer must use an actual
surjective homomorphism separately. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootOrdinaryGenerators
open CFSGSerreQuadraticMatrix

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)
    (K : Type) [Field K]

def parameterHom (neg : Bool) (i : Fin r) :
    Multiplicative K →* canonicalElementaryGroup D K where
  toFun a := canonicalElementaryRoot D K neg i a.toAdd
  map_one' := Subtype.ext (canonicalRoot_zero D K neg i)
  map_mul' a b := Subtype.ext (canonicalRoot_add D K neg i a.toAdd b.toAdd).symm

theorem parameter_ranges_generate :
    (⨆ j : Bool × Fin r, (parameterHom D K j.1 j.2).range) = ⊤ := by
  apply top_unique
  have hh := CFSGSerreSquareZeroMatrix.elementaryRootSet_generate K (canonicalRoot D K)
  rw [← hh]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨neg,i,t,rfl⟩
  have hle : (parameterHom D K neg i).range ≤
      ⨆ j : Bool × Fin r, (parameterHom D K j.1 j.2).range :=
    le_iSup_of_le (neg,i) le_rfl
  exact hle ⟨Multiplicative.ofAdd t,rfl⟩

theorem genRank_le_twice_rank_mul_finrank [Finite K]
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) K] [Module.Finite (ZMod p) K] :
    MarkedC4.genRank (canonicalElementaryGroup D K) ≤
      (2*r)*Module.finrank (ZMod p) K := by
  letI : Fintype K := Fintype.ofFinite K
  have hh := FiniteHomFamilyOrdinaryGenerators.genRank_le_sum
    (fun _ : Bool × Fin r => Multiplicative K)
    (fun j => parameterHom D K j.1 j.2) (parameter_ranges_generate D K)
  have hsum : (∑ _j : Bool × Fin r, MarkedC4.genRank (Multiplicative K)) ≤
      (2*r)*Module.finrank (ZMod p) K := by
    calc
      _ ≤ ∑ _j : Bool × Fin r, Module.finrank (ZMod p) K :=
        Finset.sum_le_sum (fun _ _ => PrimeFieldBasisOrdinaryGenerators.genRank_le_finrank p)
      _ = (2*r)*Module.finrank (ZMod p) K := by simp
  exact hh.trans hsum

theorem exists_generating_finset [Finite K]
    (p : ℕ) [Fact p.Prime] [Module (ZMod p) K] [Module.Finite (ZMod p) K] :
    ∃ S : Finset (canonicalElementaryGroup D K),
      Subgroup.closure (S : Set (canonicalElementaryGroup D K)) = ⊤ ∧
        S.card ≤ (2*r)*Module.finrank (ZMod p) K := by
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := canonicalElementaryGroup D K)
  exact ⟨S,hgen,hS.le.trans (genRank_le_twice_rank_mul_finrank D K p)⟩

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootOrdinaryGenerators
