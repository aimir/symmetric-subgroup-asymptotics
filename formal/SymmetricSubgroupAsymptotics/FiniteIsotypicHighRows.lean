import SymmetricSubgroupAsymptotics.FiniteIsotypicSmallRows

/-! The complementary high-multiplicity module and detection of its
scalar action on one actual simple constituent of each canonical row. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteIsotypicRowData

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (D : FiniteIsotypicRowData R M)

def highIndex (t : ℕ) := {i : isotypicComponents R M // t<D.multiplicity i}

instance highIndex_finite (t : ℕ) [Finite (isotypicComponents R M)] :
    Finite (D.highIndex t) := by
  unfold highIndex
  infer_instance

def highModule (t : ℕ) : Submodule R M := ⨆ i : D.highIndex t, i.val.val

theorem low_sup_high [Finite M] [IsSemisimpleModule R M] (t : ℕ) :
    D.lowModule t⊔D.highModule t=⊤ := by
  apply top_unique
  rw [←sSup_isotypicComponents R M]
  apply sSup_le
  intro P hP
  let i : isotypicComponents R M := ⟨P,hP⟩
  by_cases hi : D.multiplicity i≤t
  · exact (le_iSup (fun j : D.lowIndex t => j.val.val) ⟨i,hi⟩).trans le_sup_left
  · exact (le_iSup (fun j : D.highIndex t => j.val.val) ⟨i,by omega⟩).trans le_sup_right

/-- A scalar acts identically on a homogeneous row if it does so on its
retained actual simple constituent. -/
theorem scalar_identity_on_row (i : isotypicComponents R M) (r : R)
    (hr : ∀ s : D.simplePart i, r • s=s) : ∀ x : i.val, r • x=x := by
  intro x
  apply (D.rowEquiv i).injective
  rw [(D.rowEquiv i).map_smul]
  funext j
  exact hr _

/-- Detect the whole selected high module through exactly one original
simple constituent of each of its isotypic rows. -/
theorem scalar_identity_on_high (t : ℕ) (r : R)
    (hr : ∀ i : D.highIndex t, ∀ s : D.simplePart i.val, r • s=s)
    (x : M) (hx : x∈D.highModule t) : r • x=x := by
  refine Submodule.iSup_induction (fun i : D.highIndex t => i.val.val)
    (motive := fun y : M => r • y=y) hx ?_ ?_ ?_
  · intro i y hy
    have h := D.scalar_identity_on_row i.val r (hr i) ⟨y,hy⟩
    exact congrArg Subtype.val h
  · exact smul_zero r
  · intro y z hy hz
    rw [smul_add,hy,hz]

end SymmetricSubgroupAsymptotics.FiniteIsotypicRowData
