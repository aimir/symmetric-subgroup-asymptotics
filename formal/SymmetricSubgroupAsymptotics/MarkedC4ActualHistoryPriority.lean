import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessHistorySelection

/-! A fixed ORIGINAL normal-chain history determines all actual quotient
priorities. Thus an occupied history's selected-order inequalities hold
for every subgroup in its fibre, including enlarged suffix source fibres. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryPriority
open RDTExcessStructure ActualExcessHistorySelection ActualPeelNormalChains

def normalPriority (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    (N : {N : Subgroup G // N.Normal}) : ℕ :=
  letI : N.val.Normal := N.property
  if ¬∀ x y : G ⧸ N.val,x*y=y*x then
    if HasExcess G n 2 then (if n=8 then 3 else 2)
    else if HasExcess G n 1 ∧
      (∃ V : Subgroup (G ⧸ N.val),V.Normal ∧ (n : ℝ)/4<(normalGen V : ℝ)) then 1 else 0
  else 0

variable {t : ℕ} (degree : Fin t → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
  (M : Type) [Group M]
  (J : Subgroup ((∀ i,G i) × M))
  (hJ : ∀ i,Function.Surjective (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) J i))

theorem priority_eq_normal (S : Finset (Fin t)) (i : Fin t) :
    priority degree G M J hJ S i=
      normalPriority (degree i) (G i)
        ⟨factor (fun j => ↥(G j)) J S i,factor_normal (fun j => ↥(G j)) J hJ S i⟩ := by
  simp only [priority,Nonabelian,BadQuarter,normalPriority,
    ActualExcessHistorySelection.Quotient,ActualExcessHistorySelection.quotientGroup]
  split_ifs <;> first | rfl | contradiction

/-- Exact normal-factor equality suffices; no source-rank or counting
condition is required to transport the finite selection inequalities. -/
theorem priority_congr
    (K : Subgroup ((∀ i,G i) × M))
    (hK : ∀ i,Function.Surjective (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) K i))
    (S : Finset (Fin t)) (i : Fin t)
    (hfactor : factor (fun j => ↥(G j)) J S i=factor (fun j => ↥(G j)) K S i) :
    priority degree G M J hJ S i=priority degree G M K hK S i := by
  rw [priority_eq_normal,priority_eq_normal]
  apply congrArg (normalPriority (degree i) (G i))
  exact Subtype.ext hfactor

theorem priority_congr_of_chains
    (K : Subgroup ((∀ i,G i) × M))
    (hK : ∀ i,Function.Surjective (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) K i))
    (e : Equiv.Perm (Fin t))
    (hrows : normalChains (fun j => ↥(G j)) J e=normalChains (fun j => ↥(G j)) K e)
    (m i : Fin t) :
    priority degree G M J hJ (remaining e m.val) i=
      priority degree G M K hK (remaining e m.val) i := by
  apply priority_congr degree G M J hJ K hK
  exact congrArg (fun rows : ActualQuotientTableauMenus.RowMenu (fun j => ↥(G j)) =>
    (rows i).val m) hrows

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHistoryPriority
