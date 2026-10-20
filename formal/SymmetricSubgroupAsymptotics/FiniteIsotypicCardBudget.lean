import SymmetricSubgroupAsymptotics.FiniteIsotypicHighRows
import SymmetricSubgroupAsymptotics.FiniteHighMultiplicityBudget

/-! The exact cardinal mass of the canonical homogeneous rows pays for
all high rows simultaneously. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteIsotypicRowData

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] (D : FiniteIsotypicRowData R M)

/-- Actual coordinates for the chosen row charts. -/
def coordinates : M ≃ₗ[R] ((i : isotypicComponents R M) →
    Fin (D.multiplicity i) → D.simplePart i) := by
  let I := isotypicComponents R M
  letI : Module.Finite R M := Module.Finite.of_finite
  letI : Fintype I := Fintype.ofFinite I
  have hind : iSupIndep (fun i : I => i.val) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)
  have htop : (⨆ i : I, i.val)=⊤ :=
    (sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents R M)
  let E : M ≃ₗ[R] (i : I) → i.val :=
    (hind.linearEquiv htop).symm.trans
      (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun i : I => i.val))
  exact E.trans (LinearEquiv.piCongrRight D.rowEquiv)

theorem card_eq_prod [Fintype (isotypicComponents R M)] :
    Nat.card M=∏ i, Nat.card (D.simplePart i)^D.multiplicity i := by
  rw [Nat.card_congr D.coordinates.toEquiv,Nat.card_pi]
  simp only [Nat.card_fun,Nat.card_fin]

theorem omega_card_eq_sum [Fintype (isotypicComponents R M)] :
    MarkedC4.AbelianSectionSize.omega (Nat.card M)=
      ∑ i, D.multiplicity i * MarkedC4.AbelianSectionSize.omega (Nat.card (D.simplePart i)) := by
  rw [D.card_eq_prod]
  exact MarkedC4.AbelianSectionSize.omega_prod_pow Finset.univ _ _
    (fun i _ => Nat.card_pos.ne')

theorem simple_card_two_le (i : isotypicComponents R M) :
    2 ≤ Nat.card (D.simplePart i) := by
  letI : IsSimpleModule R (D.simplePart i) := D.simple i
  letI : Nontrivial (D.simplePart i) := IsSimpleModule.nontrivial R (D.simplePart i)
  exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance

theorem highIndex_card_le_sqrt (a : ℕ)
    (ha : MarkedC4.AbelianSectionSize.omega (Nat.card M)≤a) :
    Nat.card (D.highIndex a.sqrt)≤a.sqrt := by
  letI : Module.Finite R M := Module.Finite.of_finite
  letI : Fintype (isotypicComponents R M) := Fintype.ofFinite _
  have h := MarkedC4.AbelianSectionSize.highMultiplicity_card_le_sqrt
    (fun i => Nat.card (D.simplePart i)) D.multiplicity a D.simple_card_two_le
    (by rw [← D.omega_card_eq_sum]; exact ha)
  simpa only [highIndex,Nat.card_eq_fintype_card,Fintype.card_subtype] using h

end SymmetricSubgroupAsymptotics.FiniteIsotypicRowData
