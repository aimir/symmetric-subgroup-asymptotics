import SymmetricSubgroupAsymptotics.PrimitiveBlockFibre
import SymmetricSubgroupAsymptotics.ImprimitiveChiefHead
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-! An actual minimal block choice for an original transitive action.
The quotient map, local primitive image, exact degree product and original
normal top image are derived from a cover of the point stabilizer. The
final natural-number recurrence is ready for degree induction, with no
primitive numerical bound or finite classification included as evidence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {A Ω : Type} [Group A] [MulAction A Ω]
variable [MulAction.IsPretransitive A Ω] (ω₀ : Ω)

structure OriginalMinimalBlock where
  subgroup : Subgroup A
  covers : MulAction.stabilizer A ω₀ ⋖ subgroup
  proper : subgroup < ⊤

theorem originalMinimalBlock_nonempty [Finite A] [Finite Ω] [Nontrivial Ω]
    (hn : ¬MulAction.IsPreprimitive A Ω) :
    Nonempty (OriginalMinimalBlock (A := A) ω₀) := by
  obtain ⟨H, hH, hHt⟩ := originalPointStabilizer_exists_proper_cover ω₀ hn
  exact ⟨⟨H, hH, hHt⟩⟩

namespace OriginalMinimalBlock

variable {ω₀} (D : OriginalMinimalBlock (A := A) ω₀)

abbrev Points : Type := A ⧸ D.subgroup

abbrev base : D.Points := ((1 : A) : A ⧸ D.subgroup)

def map : Ω → D.Points := originalTransitiveBlockMap ω₀ D.subgroup

theorem map_equivariant (a : A) (ω : Ω) : D.map (a • ω) = a • D.map ω :=
  originalTransitiveBlockMap_equivariant ω₀ D.subgroup D.covers.le a ω

theorem map_surjective : Function.Surjective D.map :=
  originalTransitiveBlockMap_surjective ω₀ D.subgroup D.covers.le

theorem map_base : D.map ω₀ = D.base :=
  originalTransitiveBlockMap_base ω₀ D.subgroup D.covers.le

abbrev Fibre : Type := originalBlockFibre D.map D.base

abbrev Component : Subgroup (Equiv.Perm D.Fibre) :=
  originalBlockComponent D.map D.map_equivariant D.base

theorem component_preprimitive : MulAction.IsPreprimitive D.Component D.Fibre := by
  apply originalBlockComponent_preprimitive D.map D.map_equivariant D.base ω₀ D.map_base
  change MulAction.stabilizer A ω₀ ⋖ MulAction.stabilizer A ((1 : A) : A ⧸ D.subgroup)
  rw [MulAction.stabilizer_quotient]
  exact D.covers

theorem degree_product : Nat.card D.Fibre * Nat.card D.Points = Nat.card Ω :=
  originalTransitiveBlock_degree_product ω₀ D.subgroup D.covers.le

theorem degrees_ge_two [Finite A] : 2 ≤ Nat.card D.Fibre ∧ 2 ≤ Nat.card D.Points :=
  originalTransitiveBlock_factors_ge_two ω₀ D.subgroup D.covers.lt D.proper

theorem degrees_lt [Finite A] : Nat.card D.Fibre < Nat.card Ω ∧
    Nat.card D.Points < Nat.card Ω := by
  obtain ⟨hr, hs⟩ := D.degrees_ge_two
  have hprod := D.degree_product
  constructor
  · have h := Nat.mul_lt_mul_of_pos_left (show 1 < Nat.card D.Points from hs)
      (show 0 < Nat.card D.Fibre by omega)
    simpa only [mul_one, hprod] using h
  · have h := Nat.mul_lt_mul_of_pos_right (show 1 < Nat.card D.Fibre from hr)
      (show 0 < Nat.card D.Points by omega)
    simpa only [one_mul, hprod] using h

/-- The original permutation homomorphism on the constructed quotient. -/
abbrev topMap : A →* Equiv.Perm D.Points := MulAction.toPermHom A D.Points

/-- The actual top permutation group used for faithful degree induction. -/
abbrev Top : Subgroup (Equiv.Perm D.Points) := D.topMap.range

theorem top_pretransitive : MulAction.IsPretransitive D.Top D.Points := by
  constructor
  intro x y
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A x y
  exact ⟨D.topMap.rangeRestrict a, ha⟩

theorem top_faithful : FaithfulSMul D.Top D.Points := inferInstance

theorem top_finite [Finite A] : Finite D.Top :=
  Finite.of_surjective D.topMap.rangeRestrict D.topMap.rangeRestrict_surjective

theorem top_head_eq (p : ℕ) [Fact p.Prime] (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p (normalChainQuotient D.topMap.ker N)) =
      Module.finrank (ZMod p) (primeRelativeCharacters p (originalNormalRange D.topMap N)) :=
  primeRelativeHead_original_range p D.topMap N

/-- The actual minimal-block recurrence with the normal top image in
its literal permutation range. Both recursive degrees are smaller by
`degrees_lt`; the primitive density and top induction are separate. -/
theorem head_bound_nat [Finite A] [FaithfulSMul A Ω]
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries D.Component) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      actualChiefSeriesTernaryWeight c * ternaryIndexWidth (Nat.card D.Points) +
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 (originalNormalRange D.topMap N)) := by
  have h := originalImprimitiveChiefHead_bound D.map D.map_equivariant D.base N c
  rw [primeRelativeHead_original_range 3 D.topMap N] at h
  exact_mod_cast h

end OriginalMinimalBlock
end SymmetricSubgroupAsymptotics
