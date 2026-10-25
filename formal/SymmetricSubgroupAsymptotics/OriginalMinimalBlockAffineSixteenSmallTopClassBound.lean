import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.OriginalBlockComponentConjugation
import SymmetricSubgroupAsymptotics.AffineDegreeSixteenSubgroupClassGap
import SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound

/-! The stronger actual binary centralizer count pays original actions
with two or three affine blocks of size16. A single base profile supplies
the all-subgroup gap; literal component conjugation transports every
original coordinate subgroup into it. No profile family, supplied
capacity, split ambient action or subgroup-class monotonicity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

theorem class_cube_le_of_affine_sixteen_small_top
    (P : PrimitiveAffineProfile D.Component D.Fibre)
    (hblocks : Nat.card D.Points = 2 ∨ Nat.card D.Points = 3)
    (hdegree : Nat.card D.Fibre = 16) :
    Nat.card (ConjClasses A)^3 ≤ 5^(Nat.card Ω-1) := by
  letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp
    (by have h := D.degrees_ge_two.1; omega)
  let origin : D.Fibre := ⟨ω₀,D.map_base⟩
  apply SmallTopLargePrimitiveComponentClassBound.class_cube_le_of_subnormal_component_gaps
    D.map D.map_equivariant 16 (by decide) hblocks
    (fun x => (D.fibre_card_at x).trans hdegree)
  intro x L _hL
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A D.base x
  let j := OriginalBlockComponentConjugation.componentEmbedding
    D.map D.map_equivariant D.base x g hg
  have hj : Function.Injective j := OriginalBlockComponentConjugation.componentEmbedding_injective
    D.map D.map_equivariant D.base x g hg
  let f : L →* D.Component := j.comp L.subtype
  let e : L ≃* f.range := MonoidHom.ofInjective (hj.comp Subtype.val_injective)
  have hc : Nat.card (ConjClasses L) ≤ Nat.card (ConjClasses f.range) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  have hgap := AffineDegreeSixteenSubgroupClassGap.subgroup_class_cube_gap
    P D.component_preprimitive origin hdegree f.range
  exact (Nat.pow_le_pow_left hc 3).trans (by simpa only [hdegree] using hgap)

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
