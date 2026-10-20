import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Finiteness.Basic

/-! Actual finite isotypic coordinates for a semisimple module. The simple
rows are submodules of the original module and are pairwise nonisomorphic.
This is algebraic preparation for bounded nilpotent-core generation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- The canonical nonzero isotypic components yield finite homogeneous
rows with genuine simple constituents of the original module. -/
theorem finite_isotypic_coordinates
    (R M : Type) [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    [IsSemisimpleModule R M] :
    ∃ (d : isotypicComponents R M → ℕ)
      (S : isotypicComponents R M → Submodule R M),
      (∀ i, 0<d i) ∧ (∀ i, IsSimpleModule R (S i)) ∧
      (∀ i : isotypicComponents R M, S i ≤ (i : Submodule R M)) ∧
      (∀ i j, Nonempty (S i ≃ₗ[R] S j) → i=j) ∧
      Nonempty (M ≃ₗ[R] ((i : isotypicComponents R M) → Fin (d i) → S i)) := by
  let I := isotypicComponents R M
  letI : Module.Finite R M := Module.Finite.of_finite
  letI : Fintype I := Fintype.ofFinite I
  letI (i : I) : Module.Finite R i.val := Module.Finite.of_finite
  have hrow (i : I) : ∃ (n : ℕ) (_ : NeZero n) (S : Submodule R M),
      S ≤ (i : Submodule R M) ∧ IsSimpleModule R S ∧ Nonempty (i.val ≃ₗ[R] Fin n → S) :=
    (IsIsotypic.isotypicComponents i.property).submodule_linearEquiv_fun
  choose d hd S hle hsimple e using hrow
  letI (i : I) : IsSimpleModule R (S i) := hsimple i
  have hci (i : I) : i.val=isotypicComponent R M (S i) :=
    eq_isotypicComponent_of_le i.property (hle i)
  have hsep : ∀ i j : I, Nonempty (S i ≃ₗ[R] S j) → i=j := by
    intro i j ⟨f⟩
    apply Subtype.ext
    rw [hci i,hci j]
    exact f.isotypicComponent_eq
  have hind : iSupIndep (fun i : I => i.val) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)
  have htop : (⨆ i : I, i.val)=⊤ :=
    (sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents R M)
  let E : M ≃ₗ[R] (i : I) → i.val :=
    (hind.linearEquiv htop).symm.trans (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun i : I => i.val))
  refine ⟨d,S,fun i => Nat.pos_of_ne_zero (hd i).out,hsimple,hle,hsep,?_⟩
  exact ⟨E.trans (LinearEquiv.piCongrRight (fun i => (e i).some))⟩

end SymmetricSubgroupAsymptotics
