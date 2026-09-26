import SymmetricSubgroupAsymptotics.FiniteCayleyReflection
import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Upper order bounds from finite encoded generator transitions

An order upper bound needs only an encoded identity and closure of the finite
row set under the original generators. Parent words, row reachability and row
injectivity are unnecessary. For a finite ambient group, subgroup generation
agrees with positive-word generation, so every original generated element has
a row. Faithfulness of the encoding then injects the generated subgroup into
the row index type.

Extraneous rows need not encode actual group elements or lie in the generated
subgroup. Accordingly the weaker certificate proves one-sided coverage and an
order upper bound, not equality of the row set with the original subgroup.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G ι Code : Type*} [Group G]
variable {generators : ι → G} {E : GeneratorEncoding generators Code} {n : ℕ}

/-- The existing stronger Cayley certificate supplies a row surjection;
injectivity of its rows is not needed for an upper bound. -/
theorem EncodedCayleyCertificate.card_closure_le [Finite G]
    (C : EncodedCayleyCertificate E n) :
    Nat.card (Subgroup.closure (Set.range generators)) ≤ n := by
  let f : Fin n → Subgroup.closure (Set.range generators) := fun i =>
    ⟨C.toCayley.elements i, (C.toCayley.mem_closure_iff _).mpr ⟨i, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨i, hi⟩ := (C.toCayley.mem_closure_iff g).mp hg
    exact ⟨i, Subtype.ext hi⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf

/-- Finite code rows containing the identity and closed under each original
generator. There is deliberately no reachability or injectivity condition. -/
structure EncodedOrderBoundCertificate
    (E : GeneratorEncoding generators Code) (n : ℕ) where
  rows : Fin n → Code
  identity : Fin n
  identity_eq : rows identity = E.one
  next : Fin n → ι → Fin n
  next_eq : ∀ i j, rows (next i j) = E.step (rows i) j

namespace EncodedOrderBoundCertificate

variable (C : EncodedOrderBoundCertificate E n)

/-- Every positive word in the original generators has a code row. -/
theorem covers_submonoid (g : G)
    (hg : g ∈ Submonoid.closure (Set.range generators)) :
    ∃ i, C.rows i = E.encode g := by
  induction hg using Submonoid.closure_induction_right with
  | one =>
    exact ⟨C.identity, C.identity_eq.trans E.encode_one.symm⟩
  | mul_right x _ y hy ih =>
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨i, hi⟩ := ih
    refine ⟨C.next i j, ?_⟩
    rw [C.next_eq, hi, E.encode_step]

/-- Finite ambient groups require no extra inverse-transition certificate:
their original subgroup closure is already the positive-word closure. -/
theorem covers [Finite G] (g : G)
    (hg : g ∈ Subgroup.closure (Set.range generators)) :
    ∃ i, C.rows i = E.encode g := by
  apply C.covers_submonoid g
  have hm : g ∈ (Subgroup.closure (Set.range generators)).toSubmonoid := hg
  rw [Subgroup.closure_toSubmonoid_of_finite] at hm
  exact hm

include C in
/-- Actual original order bound from finite encoded right-generator closure.
No row is assumed to be reachable, and different rows may have equal codes. -/
theorem card_closure_le [Finite G] :
    Nat.card (Subgroup.closure (Set.range generators)) ≤ n := by
  classical
  let f : Subgroup.closure (Set.range generators) → Fin n :=
    fun g => Classical.choose (C.covers g g.property)
  have hf (g : Subgroup.closure (Set.range generators)) :
      C.rows (f g) = E.encode (g : G) :=
    Classical.choose_spec (C.covers g g.property)
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply E.injective
    rw [← hf x, ← hf y, h]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hinj

end EncodedOrderBoundCertificate

/-- Forget parent/reachability data when only an order upper bound is needed. -/
def EncodedCayleyCertificate.toOrderBound
    (C : EncodedCayleyCertificate E n) : EncodedOrderBoundCertificate E n where
  rows := C.rows
  identity := C.identity
  identity_eq := C.identity_eq
  next := C.next
  next_eq := C.next_eq

end SymmetricSubgroupAsymptotics

end
