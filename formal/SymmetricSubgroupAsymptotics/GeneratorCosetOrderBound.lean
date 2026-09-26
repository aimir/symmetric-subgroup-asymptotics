import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Upper order bounds from generator transitions between cosets

The original generated subgroup is covered by finitely many right cosets
`K * representative`. Only the identity coset and right-generator transition
defects are checked. The subgroup `K` need not be normal or contained in the
generated subgroup; representatives need not be reachable or distinct.

This proves an upper bound on the actual generated group. It does not assert
that the cosets are disjoint, exhaust the ambient group, or form a quotient.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G ι : Type*} [Group G]

/-- A one-sided finite coset cover closed under the original generators.
The orientation of `step_mem` is exactly the one needed for `K * r` cosets. -/
structure GeneratorCosetOrderBoundCertificate
    (generators : ι → G) (K : Subgroup G) (q : ℕ) where
  representatives : Fin q → G
  identity : Fin q
  identity_mem : representatives identity ∈ K
  next : Fin q → ι → Fin q
  step_mem : ∀ i j, representatives i * generators j *
    (representatives (next i j))⁻¹ ∈ K

namespace GeneratorCosetOrderBoundCertificate

variable {generators : ι → G} {K : Subgroup G} {q : ℕ}
    (C : GeneratorCosetOrderBoundCertificate generators K q)

/-- Every original positive word lies in one of the supplied right cosets. -/
theorem covers_submonoid (x : G)
    (hx : x ∈ Submonoid.closure (Set.range generators)) :
    ∃ i : Fin q, ∃ k : K, x = (k : G) * C.representatives i := by
  induction hx using Submonoid.closure_induction_right with
  | one =>
    refine ⟨C.identity, ⟨(C.representatives C.identity)⁻¹,
      K.inv_mem C.identity_mem⟩, ?_⟩
    simp only [inv_mul_cancel]
  | mul_right x _ y hy ih =>
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨i, k, hk⟩ := ih
    let a : K := ⟨C.representatives i * generators j *
      (C.representatives (C.next i j))⁻¹, C.step_mem i j⟩
    refine ⟨C.next i j, k * a, ?_⟩
    change x * generators j = (k : G) *
      (C.representatives i * generators j *
        (C.representatives (C.next i j))⁻¹) * C.representatives (C.next i j)
    rw [hk]
    simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- Finite ambient groups need no separate inverse transition witnesses. -/
theorem covers [Finite G] (x : G)
    (hx : x ∈ Subgroup.closure (Set.range generators)) :
    ∃ i : Fin q, ∃ k : K, x = (k : G) * C.representatives i := by
  apply C.covers_submonoid x
  have hm : x ∈ (Subgroup.closure (Set.range generators)).toSubmonoid := hx
  rw [Subgroup.closure_toSubmonoid_of_finite] at hm
  exact hm

include C in
/-- The actual generated subgroup injects into a representative index and
an element of `K`. No injectivity of the supplied representatives is needed. -/
theorem card_closure_le [Finite G] :
    Nat.card (Subgroup.closure (Set.range generators)) ≤ q * Nat.card K := by
  classical
  let S := Subgroup.closure (Set.range generators)
  have hrep (x : S) : ∃ p : Fin q × K,
      (x : G) = (p.2 : G) * C.representatives p.1 := by
    obtain ⟨i, k, hk⟩ := C.covers x x.property
    exact ⟨(i, k), hk⟩
  let f : S → Fin q × K := fun x => Classical.choose (hrep x)
  have hf (x : S) : (x : G) = ((f x).2 : G) * C.representatives (f x).1 :=
    Classical.choose_spec (hrep x)
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    calc
      (x : G) = ((f x).2 : G) * C.representatives (f x).1 := hf x
      _ = ((f y).2 : G) * C.representatives (f y).1 :=
        congrArg (fun p : Fin q × K => (p.2 : G) * C.representatives p.1) h
      _ = (y : G) := (hf y).symm
  simpa only [Nat.card_prod, Nat.card_fin] using
    Nat.card_le_card_of_injective f hinj

end GeneratorCosetOrderBoundCertificate
end SymmetricSubgroupAsymptotics

end
