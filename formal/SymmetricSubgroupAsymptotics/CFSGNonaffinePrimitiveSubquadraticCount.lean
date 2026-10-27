import SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitivePolylogRank
import SymmetricSubgroupAsymptotics.FiniteSubgroupSmallOrderCount
import SymmetricSubgroupAsymptotics.FactorialUniformPolylogSubquadraticCount

/-! Literal labelled nonaffine primitive subgroups, across ALL CFSG models.
This closes the primitive nonaffine counting sector, not the imprimitive
extension/lift count required for all transitive groups. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitiveSubquadraticCount
open PrimitiveSocleRawStructure

def InSector (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  MulAction.IsPreprimitive H (Fin n) ∧ Nonempty (NonaffineData H (Fin n))

abbrev Sector (n : ℕ) := {H : Subgroup (Equiv.Perm (Fin n)) // InSector n H}

local instance (n : ℕ) : Fintype (Sector n) := Fintype.ofFinite _

theorem exists_uniform_count_budget (hCFSG : CFSG.CFSGClassification) :
    ∃ A : ℕ, ∀ n : ℕ, 2≤n →
      Nat.card (Sector n)≤n.factorial^(A*(Nat.log 2 n+2)^2) := by
  obtain ⟨A,hA⟩ := CFSGNonaffinePrimitivePolylogRank.exists_uniform_rank_budget hCFSG
  refine ⟨A,?_⟩
  intro n hn
  let B := A*(Nat.log 2 n+2)^2
  have hr : ∀ H : Sector n,MarkedC4.genRank H.val≤B := by
    intro H
    obtain ⟨hp,⟨D⟩⟩ := H.property
    letI := hp
    letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
      (by simpa only [Nat.card_fin] using (show 1<n by omega))
    simpa only [Nat.card_fin] using hA D
  let f : Sector n → {H : Subgroup (Equiv.Perm (Fin n)) // MarkedC4.genRank H≤B} :=
    fun H => ⟨H.val,hr H⟩
  have hf : Function.Injective f := by
    intro H K h
    exact Subtype.ext (congrArg
      (fun a : {U : Subgroup (Equiv.Perm (Fin n)) // MarkedC4.genRank U≤B} => a.val) h)
  have hh := (Nat.card_le_card_of_injective f hf).trans
    (FiniteSubgroupSmallOrderCount.card_rank_bounded_subgroups_le
      (G := Equiv.Perm (Fin n)) B)
  simpa only [Nat.card_perm,Nat.card_fin,B] using hh

theorem sector_subquadratic (hCFSG : CFSG.CFSGClassification) :
    SubquadraticMenuIndexCount Sector := by
  obtain ⟨A,hA⟩ := exists_uniform_count_budget hCFSG
  exact FactorialUniformPolylogSubquadraticCount.subquadratic_of_factorial_budget A hA

end SymmetricSubgroupAsymptotics.CFSGNonaffinePrimitiveSubquadraticCount
