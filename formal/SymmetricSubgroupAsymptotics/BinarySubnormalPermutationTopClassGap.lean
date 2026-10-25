import SymmetricSubgroupAsymptotics.BinarySubnormalSymmetricTopClassGap
import SymmetricSubgroupAsymptotics.PermutationalWreathTransport

/-! Relabel the SAME coordinates and actual top range by an honest
finite-set equivalence. No transitivity is introduced by this chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinarySubnormalPermutationTopClassGap
open WreathHomProjectionRange

variable {A C I : Type} [Group A] [CommGroup C] [Finite A] [Finite C] [Finite I]

theorem class_cube_gap_of_subnormal_top_range
    (hC : Nat.card C=2) (hn : 10 ≤ Nat.card I)
    (f : A →* PermutationalWreathProduct C (Equiv.Perm I) I)
    (hf : Function.Injective f) (hR : (topProjection f).range.IsSubnormal) :
    Nat.card (ConjClasses A)^3 ≤ 5^(2*Nat.card I-2) := by
  let c : I ≃ Fin (Nat.card I) := Finite.equivFinOfCardEq rfl
  let e : Equiv.Perm I ≃* Equiv.Perm (Fin (Nat.card I)) := c.permCongrHom
  have hc : ∀ (q : Equiv.Perm I) (i : I), c (q • i) = e q • c i := by
    intro q i
    change c (q i) = c.permCongr q (c i)
    simp only [Equiv.permCongr_apply,Equiv.symm_apply_apply]
  let w := PermutationalWreathProduct.transport (D := C) e c hc
  let f' := w.toMonoidHom.comp f
  have hf' : Function.Injective f' := w.injective.comp hf
  have hp : topProjection f' = e.toMonoidHom.comp (topProjection f) := by
    ext a
    rfl
  have hR' : (topProjection f').range.IsSubnormal := by
    rw [hp,MonoidHom.range_comp]
    exact Subgroup.IsSubnormal.map e.surjective hR
  exact BinarySubnormalSymmetricTopClassGap.class_cube_gap_of_subnormal_top_range
    (Nat.card I) hC hn f' hf' hR'

end SymmetricSubgroupAsymptotics.BinarySubnormalPermutationTopClassGap
