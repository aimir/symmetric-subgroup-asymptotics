import SymmetricSubgroupAsymptotics.TransitiveBinaryActionCount
import Mathlib.Data.Quot

/-!
# Complete original transitive binary action representatives

Classes are formed from actual subgroups of the original permutation group,
using conjugation by actual permutations of the same points. One original
subgroup is chosen per class. The choice introduces no additional labels.
Neither abstract isomorphism nor a supplied catalogue is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

/-- Actual binary transitive subgroups on the given original points. -/
abbrev BinaryTransitiveAction (X : Type) :=
  {U : Subgroup (Equiv.Perm X) // IsPGroup 2 U ∧ MulAction.IsPretransitive U X}

/-- Equality of action classes means actual ambient permutation conjugacy. -/
def binaryTransitiveActionSetoid (X : Type) : Setoid (BinaryTransitiveAction X) where
  r A B := ∃ c : Equiv.Perm X, MulAut.conj c • A.1 = B.1
  iseqv := {
    refl := fun A => ⟨1, by rw [map_one, one_smul]⟩
    symm := by
      rintro A B ⟨c,hc⟩
      refine ⟨c⁻¹,?_⟩
      rw [← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    trans := by
      rintro A B C ⟨c,hc⟩ ⟨d,hd⟩
      refine ⟨d*c,?_⟩
      rw [map_mul, mul_smul, hc, hd] }

/-- The complete class index, with no duplicate representative labels. -/
abbrev BinaryTransitiveActionClass (X : Type) :=
  Quotient (binaryTransitiveActionSetoid X)

namespace BinaryTransitiveActionClass

variable {X : Type}

instance instFinite [Finite X] : Finite (BinaryTransitiveActionClass X) := by
  unfold BinaryTransitiveActionClass
  infer_instance

instance instFintype [Finite X] : Fintype (BinaryTransitiveActionClass X) :=
  Fintype.ofFinite _

/-- A single original subgroup selected from each actual conjugacy class. -/
def representative (i : BinaryTransitiveActionClass X) : Subgroup (Equiv.Perm X) :=
  i.out.1

theorem representative_isPGroup (i : BinaryTransitiveActionClass X) :
    IsPGroup 2 i.representative := i.out.2.1

instance representative_pretransitive (i : BinaryTransitiveActionClass X) :
    MulAction.IsPretransitive i.representative X := i.out.2.2

/-- Any actual conjugacy between two chosen original subgroups forces
their class labels equal, including conjugacy by the identity. -/
theorem representative_separated
    (i j : BinaryTransitiveActionClass X) (c : Equiv.Perm X)
    (hc : MulAut.conj c • i.representative = j.representative) : i = j := by
  have h : Quotient.mk (binaryTransitiveActionSetoid X) i.out =
      Quotient.mk (binaryTransitiveActionSetoid X) j.out := Quotient.sound ⟨c,hc⟩
  exact (Quotient.out_eq i).symm.trans (h.trans (Quotient.out_eq j))

/-- Every actual binary transitive subgroup is conjugate to a chosen
representative by an original permutation of the same point set. -/
theorem representative_cover (U : Subgroup (Equiv.Perm X))
    (hU : IsPGroup 2 U) (htrans : MulAction.IsPretransitive U X) :
    ∃ i : BinaryTransitiveActionClass X, ∃ c : Equiv.Perm X,
      MulAut.conj c • U = i.representative := by
  let A : BinaryTransitiveAction X := ⟨U,hU,htrans⟩
  let i : BinaryTransitiveActionClass X := Quotient.mk _ A
  obtain ⟨c,hc⟩ := Quotient.mk_out (s := binaryTransitiveActionSetoid X) A
  refine ⟨i,c⁻¹,?_⟩
  change MulAut.conj c • i.representative = U at hc
  rw [← hc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The complete original action-class family satisfies the proved tuple
bound, with separation now a theorem rather than an external premise. -/
theorem card_le [Finite X] (k : ℕ) (hdegree : Nat.card X = 2^k) :
    Nat.card (BinaryTransitiveActionClass X) ≤
      2^((2^k-1)*binaryCumulativeWidth k) := by
  let P : Sylow 2 (Equiv.Perm X) := Classical.choice inferInstance
  exact transitiveBinary_action_family_card_le_degree k P representative
    representative_pretransitive representative_isPGroup hdegree representative_separated

end BinaryTransitiveActionClass
end SymmetricSubgroupAsymptotics

end
