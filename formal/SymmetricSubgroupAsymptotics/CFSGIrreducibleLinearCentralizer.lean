import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! The actual linear centralizer of an irreducible representation acts
freely on nonzero vectors. In particular its order divides the number of
nonzero vectors. No splitting field or division-ring classification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGIrreducibleLinearCentralizer

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V)

/-- Literal commuting linear automorphisms of the original module. -/
def linearCentralizer : Subgroup (V ≃ₗ[k] V) where
  carrier := {e | ∀ g x, e (rho g x) = rho g (e x)}
  one_mem' := by intro g x; rfl
  mul_mem' := by
    intro e f he hf g x
    change e (f (rho g x)) = rho g (e (f x))
    rw [hf, he]
  inv_mem' := by
    intro e he g x
    apply e.injective
    change e (e.symm (rho g x)) = e (rho g (e.symm x))
    rw [e.apply_symm_apply, he, e.apply_symm_apply]

/-- Schur's injective-or-zero argument makes evaluation at one nonzero
original vector injective on the full algebra of intertwining maps. -/
theorem intertwining_evaluation_injective [Representation.IsIrreducible rho]
    (v : V) (hv : v ≠ 0) :
    Function.Injective (fun f : rho.IntertwiningMap rho => f v) := by
  intro f g hfg
  rcases Representation.IsIrreducible.injective_or_eq_zero (f - g) with hi | hz
  · have hzero : (f - g) v = (f - g) 0 := by
      rw [map_zero]
      change f v - g v = 0
      exact sub_eq_zero.mpr hfg
    exact False.elim (hv (hi hzero))
  · exact sub_eq_zero.mp hz

def centralizerIntertwiner (e : linearCentralizer rho) : rho.IntertwiningMap rho :=
  e.1.toLinearMap.intertwiningMap_of_isIntertwiningMap rho rho
    (fun g x => e.2 g x)

theorem centralizer_evaluation_injective [Representation.IsIrreducible rho]
    (v : V) (hv : v ≠ 0) :
    Function.Injective (fun e : linearCentralizer rho => e.1 v) := by
  intro e f he
  have h : centralizerIntertwiner rho e = centralizerIntertwiner rho f :=
    intertwining_evaluation_injective rho v hv he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun q : rho.IntertwiningMap rho => q x) h

theorem centralizer_card_dvd_nonzero_card [Finite V]
    [Representation.IsIrreducible rho] :
    Nat.card (linearCentralizer rho) ∣ Nat.card V - 1 := by
  let X := {v : V // v ≠ 0}
  letI : MulAction (linearCentralizer rho) X := {
    smul e v := ⟨e.1 v.1, by
      intro h
      exact v.2 (e.1.injective (h.trans (map_zero e.1).symm))⟩
    one_smul v := by apply Subtype.ext; rfl
    mul_smul e f v := by apply Subtype.ext; rfl }
  have hfree (v : X) : MulAction.stabilizer (linearCentralizer rho) v = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro e he
    apply centralizer_evaluation_injective rho v.1 v.2
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp he)
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree)
  rw [Nat.card_prod] at hcard
  have hdvd : Nat.card (linearCentralizer rho) ∣ Nat.card X := by
    rw [hcard]
    exact dvd_mul_left _ _
  have hnz : Nat.card X = Nat.card V - 1 := by
    letI : Fintype V := Fintype.ofFinite V
    simp only [X, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq]
  rwa [hnz] at hdvd

theorem centralizer_isCyclic_of_prime_nonzero_card [Finite V]
    [Representation.IsIrreducible rho] {p : ℕ} [Fact p.Prime]
    (hcard : Nat.card V - 1 = p) : IsCyclic (linearCentralizer rho) := by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [← hcard]
  exact centralizer_card_dvd_nonzero_card rho

end SymmetricSubgroupAsymptotics.CFSGIrreducibleLinearCentralizer
