import SymmetricSubgroupAsymptotics.CocycleCardinality
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Actual cocycles are determined by original generators

Evaluation on a stated generating tuple is injective on the literal
one-cocycles for the original representation. The actual projection to
first cohomology then gives its cardinal bound. No bound on the length of
the tuple, splitting of an extension, or replacement of the source group
is asserted. A finite source is unnecessary once a finite generating
tuple is supplied.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open groupCohomology

universe u
variable {k B : Type u} [CommRing k] [Group B] (A : Rep k B)

/-- Values of the original one-cocycle on the displayed original tuple. -/
def cocycleGeneratorEvaluation {ι : Type*} (generators : ι → B) :
    cocycles₁ A →ₗ[k] (ι → A) where
  toFun z i := z (generators i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Equality propagates through products and inverses using the original
action. The closure premise refers to the actual source B. -/
theorem cocycleGeneratorEvaluation_injective {ι : Type*}
    (generators : ι → B)
    (hgen : Subgroup.closure (Set.range generators) = ⊤) :
    Function.Injective (cocycleGeneratorEvaluation A generators) := by
  intro z z' heq
  let K : Subgroup B := {
    carrier := {b | z b = z' b}
    one_mem' := by
      change z 1 = z' 1
      simp only [cocycles₁_map_one]
    mul_mem' := by
      intro x y hx hy
      change z (x*y) = z' (x*y)
      rw [(mem_cocycles₁_iff z).mp z.2 x y,
        (mem_cocycles₁_iff z').mp z'.2 x y, hx, hy]
    inv_mem' := by
      intro x hx
      have hz := (mem_cocycles₁_iff z).mp z.2 x⁻¹ x
      have hz' := (mem_cocycles₁_iff z').mp z'.2 x⁻¹ x
      simp only [inv_mul_cancel, cocycles₁_map_one] at hz hz'
      rw [hx] at hz
      exact add_left_cancel (hz.symm.trans hz') }
  have hclosure : Subgroup.closure (Set.range generators) ≤ K := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact congrFun heq i
  have htop : (⊤ : Subgroup B) ≤ K := by
    rw [← hgen]
    exact hclosure
  apply cocycles₁_ext
  intro b
  exact htop (Subgroup.mem_top b)

/-- A finite original tuple bounds the number of literal cocycles.
The empty tuple case is included. -/
theorem cocycles_card_le_generator_power [Finite A] (d : ℕ)
    (generators : Fin d → B)
    (hgen : Subgroup.closure (Set.range generators) = ⊤) :
    Nat.card (cocycles₁ A) ≤ Nat.card A ^ d := by
  calc
    Nat.card (cocycles₁ A) ≤ Nat.card (Fin d → A) :=
      Nat.card_le_card_of_injective (cocycleGeneratorEvaluation A generators)
        (cocycleGeneratorEvaluation_injective A generators hgen)
    _ = Nat.card A ^ d := by rw [Nat.card_fun, Nat.card_fin]

/-- The actual first cohomology is a quotient of these same original
cocycles. Its classes need not have well-defined generator evaluations. -/
theorem firstCohomology_card_le_generator_power [Finite A] (d : ℕ)
    (generators : Fin d → B)
    (hgen : Subgroup.closure (Set.range generators) = ⊤) :
    Nat.card (H1 A) ≤ Nat.card A ^ d := by
  letI : Finite (cocycles₁ A) :=
    Finite.of_injective (cocycleGeneratorEvaluation A generators)
      (cocycleGeneratorEvaluation_injective A generators hgen)
  exact (Nat.card_le_card_of_surjective (H1π A)
    (firstCohomologyProjection_surjective A)).trans
      (cocycles_card_le_generator_power A d generators hgen)

end SymmetricSubgroupAsymptotics

end
