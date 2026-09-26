import SymmetricSubgroupAsymptotics.DerivedWordFiniteCertificate

/-! A small row code bounds the centralizer inside the actual derived
subgroup of the original generator closure. The code need cover only
commuting rows. No normal subgroup list or ambient group table is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace DerivedWordFiniteCertificate

section General

variable {G ι κ : Type*} [Group G] [Finite G]
    {g : ι → G} {words : κ → DerivedGeneratorWord ι} {n k : ℕ}

/-- Every commuting row is recovered from its code. This suffices for
an upper bound: selected rows need not commute or be distinct. -/
theorem card_centralizer_le_of_row_code
    (C : DerivedWordFiniteCertificate g words n)
    (u : Subgroup.closure (Set.range g))
    (select : Fin k → Fin n) (code : Fin n → Fin k)
    (hcover : ∀ i, C.cayley.elements i * u = u * C.cayley.elements i →
      select (code i) = i) :
    Nat.card (commutator (Subgroup.closure (Set.range g)) ⊓
      Subgroup.centralizer {u} : Subgroup (Subgroup.closure (Set.range g))) ≤ k := by
  classical
  let S : Subgroup (Subgroup.closure (Set.range g)) :=
    commutator (Subgroup.closure (Set.range g)) ⊓ Subgroup.centralizer {u}
  have row_exists (x : S) :
      ∃ i, C.cayley.elements i = (x : Subgroup.closure (Set.range g)) := by
    apply (C.cayley.mem_closure_iff _).mp
    change (x : Subgroup.closure (Set.range g)) ∈ derivedWordClosure g words
    rw [C.subgroup_eq_commutator]
    exact x.2.1
  let row (x : S) : Fin n := Classical.choose (row_exists x)
  have row_value (x : S) :
      C.cayley.elements (row x) = (x : Subgroup.closure (Set.range g)) :=
    Classical.choose_spec (row_exists x)
  have row_commutes (x : S) :
      C.cayley.elements (row x) * u = u * C.cayley.elements (row x) := by
    rw [row_value]
    exact Subgroup.mem_centralizer_singleton_iff.mp x.2.2
  have hinjective : Function.Injective (fun x : S => code (row x)) := by
    intro x y he
    have hrow : row x = row y := by
      calc
        row x = select (code (row x)) := (hcover _ (row_commutes x)).symm
        _ = select (code (row y)) := congrArg select he
        _ = row y := hcover _ (row_commutes y)
    apply Subtype.ext
    exact (row_value x).symm.trans ((congrArg C.cayley.elements hrow).trans (row_value y))
  change Nat.card S ≤ k
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_injective (fun x : S => code (row x)) hinjective

end General

section Pointwise

variable {X ι κ : Type*} [Finite X]
    {g : ι → Equiv.Perm X} {words : κ → DerivedGeneratorWord ι} {n k : ℕ}

/-- A finite permutation producer can check the coverage implication
pointwise on the original points, with ordinary kernel-checked decision. -/
theorem card_centralizer_le_of_pointwise_row_code
    (C : DerivedWordFiniteCertificate g words n)
    (u : Subgroup.closure (Set.range g))
    (select : Fin k → Fin n) (code : Fin n → Fin k)
    (hcover : ∀ i,
      (∀ x, (C.cayley.elements i : Equiv.Perm X) ((u : Equiv.Perm X) x) =
        (u : Equiv.Perm X) ((C.cayley.elements i : Equiv.Perm X) x)) →
      select (code i) = i) :
    Nat.card (commutator (Subgroup.closure (Set.range g)) ⊓
      Subgroup.centralizer {u} : Subgroup (Subgroup.closure (Set.range g))) ≤ k := by
  apply C.card_centralizer_le_of_row_code u select code
  intro i he
  apply hcover i
  intro x
  exact congrArg (fun v : Subgroup.closure (Set.range g) => (v : Equiv.Perm X) x) he

end Pointwise
end DerivedWordFiniteCertificate
end SymmetricSubgroupAsymptotics
