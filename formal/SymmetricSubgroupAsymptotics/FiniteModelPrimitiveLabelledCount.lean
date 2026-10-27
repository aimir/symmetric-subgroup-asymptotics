import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget
import SymmetricSubgroupAsymptotics.FiniteSubgroupSmallOrderCount

/-! Literal labelled primitive sector for a finite family of actual simple
models. The models need no proved order, displayed generators, or global
Finite instances. Every subgroup carries its actual nonaffine chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteModelPrimitiveLabelledCount
open PrimitiveSocleRawStructure FiniteModelPrimitiveOrdinaryBudget

variable {ι : Type} (M : ι → Type) [∀ i,Group (M i)]

def InSector (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  MulAction.IsPreprimitive H (Fin n) ∧
    ∃ D : NonaffineData H (Fin n), ∃ i : ι, Nonempty (D.Simple ≃* M i)

abbrev Sector (n : ℕ) := {H : Subgroup (Equiv.Perm (Fin n)) // InSector M n H}

theorem rank_le_budget (C n : ℕ) (hC : ∀ i,HasModelBudget (M i) C)
    (hn : 2 ≤ n) (H : Sector M n) :
    MarkedC4.genRank H.val ≤ (Nat.log 2 n+2)*C+(Nat.log 2 n)^2 := by
  obtain ⟨hp,D,i,⟨e⟩⟩ := H.property
  letI := hp
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_fin] using (show 1<n by omega))
  simpa only [Nat.card_fin] using hC i D e

theorem card_sector_le (C n : ℕ) (hC : ∀ i,HasModelBudget (M i) C)
    (hn : 2 ≤ n) :
    Nat.card (Sector M n) ≤ n.factorial^((Nat.log 2 n+2)*C+(Nat.log 2 n)^2) := by
  let B := (Nat.log 2 n+2)*C+(Nat.log 2 n)^2
  let f : Sector M n → {H : Subgroup (Equiv.Perm (Fin n)) // MarkedC4.genRank H ≤ B} :=
    fun H => ⟨H.val,rank_le_budget M C n hC hn H⟩
  have hf : Function.Injective f := by
    intro H K h
    exact Subtype.ext (congrArg
      (fun a : {U : Subgroup (Equiv.Perm (Fin n)) // MarkedC4.genRank U ≤ B} => a.val) h)
  have hh := (Nat.card_le_card_of_injective f hf).trans
    (FiniteSubgroupSmallOrderCount.card_rank_bounded_subgroups_le
      (G := Equiv.Perm (Fin n)) B)
  simpa only [Nat.card_perm,Nat.card_fin,B] using hh

/-- A single genuine finite constant pays every labelled primitive subgroup
in this entire finite-model family and every degree≥2. -/
theorem exists_uniform_count_budget [Finite ι] :
    ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n →
      Nat.card (Sector M n) ≤ n.factorial^((Nat.log 2 n+2)*C+(Nat.log 2 n)^2) := by
  obtain ⟨C,hC⟩ := finite_family_budget M
  exact ⟨C,fun n hn => card_sector_le M C n hC hn⟩

end SymmetricSubgroupAsymptotics.FiniteModelPrimitiveLabelledCount
