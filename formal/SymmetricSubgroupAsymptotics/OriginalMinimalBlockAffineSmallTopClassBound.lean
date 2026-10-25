import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.OriginalBlockComponentConjugation
import SymmetricSubgroupAsymptotics.AffineDegreeEightSubgroupClassGap
import SymmetricSubgroupAsymptotics.AffineDegreeNineSubgroupClassGap
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound

/-! Native minimal-block installation from ONE actual base affine
profile. Literal component conjugation transports all-subgroup bounds
from that base to each original coordinate image. No family of supplied
profiles, primitive-top premise or numerical capacity callback remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

private theorem small_top_base_gap_step (a : ℕ) (ha : 2 ≤ a)
    (hblocks : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3)
    (hsize : Nat.card D.Fibre = a)
    (hbase : ∀ L : Subgroup D.Component,
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (a - 2)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  apply SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
    D.map D.map_equivariant a ha hblocks (fun x => (D.fibre_card_at x).trans hsize)
  intro x L _hL
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A D.base x
  let j := OriginalBlockComponentConjugation.componentEmbedding
    D.map D.map_equivariant D.base x g hg
  have hj : Function.Injective j := OriginalBlockComponentConjugation.componentEmbedding_injective
    D.map D.map_equivariant D.base x g hg
  let f : L →* D.Component := j.comp L.subtype
  have hf : Function.Injective f := hj.comp Subtype.val_injective
  let e : L ≃* f.range := MonoidHom.ofInjective hf
  have hc : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (Nat.pow_le_pow_left hc 3).trans (hbase f.range)

theorem class_cube_le_of_affine_eight_or_nine_small_top
    (P : PrimitiveAffineProfile D.Component D.Fibre)
    (hblocks : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3)
    (hdegree : Nat.card D.Fibre = 8 ∨ Nat.card D.Fibre = 9) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp
    (by have h := D.degrees_ge_two.1; omega)
  let origin : D.Fibre := ⟨ω₀, D.map_base⟩
  apply small_top_base_gap_step D (Nat.card D.Fibre) D.degrees_ge_two.1 hblocks rfl
  intro L
  rcases hdegree with hEight | hNine
  · exact AffineDegreeEightSubgroupClassGap.subgroup_class_cube_gap
      P D.component_preprimitive origin hEight L
  · exact AffineDegreeNineSubgroupClassGap.subgroup_class_cube_gap P origin hNine L

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
