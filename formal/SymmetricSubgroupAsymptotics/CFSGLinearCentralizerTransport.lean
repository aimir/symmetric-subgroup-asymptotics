import SymmetricSubgroupAsymptotics.CFSGIrreducibleLinearCentralizer
import Mathlib.GroupTheory.Solvable

/-! Equivariant linear charts transport the literal commuting linear
automorphisms. In particular the acting representation and its centralizer
need not already have the chosen coordinate carrier. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGLinearCentralizerTransport
open CFSGIrreducibleLinearCentralizer

variable {k S V W : Type} [Field k] [Group S]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (rho : Representation k S V) (tau : Representation k S W)
    (e : V ≃ₗ[k] W) (he : ∀ s v, e (rho s v) = tau s (e v))

include he in
theorem equivariant_symm (s : S) (w : W) :
    e.symm (tau s w) = rho s (e.symm w) := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

def centralizerHom : linearCentralizer rho →* linearCentralizer tau where
  toFun c := ⟨e.symm.trans (c.val.trans e), by
    intro s w
    change e (c.val (e.symm (tau s w))) = tau s (e (c.val (e.symm w)))
    rw [equivariant_symm rho tau e he, c.property]
    exact he s (c.val (e.symm w))⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    exact e.apply_symm_apply w
  map_mul' c d := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    change e (c.val (d.val (e.symm w))) =
      e (c.val (e.symm (e (d.val (e.symm w)))))
    rw [e.symm_apply_apply]

theorem centralizerHom_injective :
    Function.Injective (centralizerHom rho tau e he) := by
  intro c d hcd
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hh := congrArg (fun f : linearCentralizer tau => e.symm (f.val (e v))) hcd
  change e.symm (e (c.val (e.symm (e v)))) =
    e.symm (e (d.val (e.symm (e v)))) at hh
  simpa only [e.symm_apply_apply] using hh

include e he in
theorem solvable_of_chart [IsSolvable (linearCentralizer tau)] :
    IsSolvable (linearCentralizer rho) :=
  solvable_of_solvable_injective (f := centralizerHom rho tau e he)
    (centralizerHom_injective rho tau e he)

end SymmetricSubgroupAsymptotics.CFSGLinearCentralizerTransport
