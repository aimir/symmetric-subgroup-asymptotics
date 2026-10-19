import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Fin

/-! Every actual order-eight subgroup of S4 is conjugate to any fixed
faithful order-eight four-point model. This is Sylow conjugacy, with no
subgroup list or catalogue membership hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CardEightPermutationConjugacy

private theorem sylow_card (B : Subgroup (Equiv.Perm (Fin 4)))
    (hB : Nat.card B=8) :
    Nat.card B=2^(Nat.card (Equiv.Perm (Fin 4))).factorization 2 := by
  rw [hB, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide +kernel

/-- A point permutation conjugates the actual image, retaining its action. -/
theorem exists_conjugator (B D : Subgroup (Equiv.Perm (Fin 4)))
    (hB : Nat.card B=8) (hD : Nat.card D=8) :
    ∃ g : Equiv.Perm (Fin 4), MulAut.conj g • B=D := by
  let P : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.ofCard B (sylow_card B hB)
  let Q : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.ofCard D (sylow_card D hD)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 4)) P Q
  refine ⟨g,?_⟩
  have hh := congrArg (fun S : Sylow 2 (Equiv.Perm (Fin 4)) => (S : Subgroup (Equiv.Perm (Fin 4)))) hg
  simpa only [Sylow.coe_subgroup_smul, P, Q, Sylow.coe_ofCard] using hh
end SymmetricSubgroupAsymptotics.CardEightPermutationConjugacy
