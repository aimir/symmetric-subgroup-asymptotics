import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourNonzeroCore
import SymmetricSubgroupAsymptotics.TransitiveDerangement
import SymmetricSubgroupAsymptotics.CyclicQuotientOfSupZPowers
import SymmetricSubgroupAsymptotics.NormalTwoKernelOddHall

/-!
# The actual soluble subgroup for the degree-four Tracey formula

For a nonzero correlated ternary core, choose a derangement in the literal
block top and lift it to the actual ambient group.  The subgroup generated
by the full ternary-core preimage and that one lift has no singleton orbit
on blocks.  Its quotient by the core preimage is literally cyclic.  These
are the group-theoretic seams in the application of Tracey's exact soluble
orbit formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- One fixed-point-free element of the literal transitive block top. -/
noncomputable def degreeFourTopDerangement
    (hs : 2 ≤ Nat.card block.Points) : block.Top := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  letI : Nontrivial block.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact Classical.choose
    (exists_fixedBy_eq_empty_of_pretransitive block.Top block.Points)

theorem degreeFourTopDerangement_fixedBy
    (hs : 2 ≤ Nat.card block.Points) :
    MulAction.fixedBy block.Points
      (degreeFourTopDerangement block hs) = ∅ := by
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  letI : Nontrivial block.Points :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact Classical.choose_spec
    (exists_fixedBy_eq_empty_of_pretransitive block.Top block.Points)

/-- An actual ambient lift of the displayed top derangement. -/
noncomputable def degreeFourAmbientDerangement
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    preE7NonPairAction w U := by
  let S := initialState hTraceyPerm block
  exact Classical.choose
    (S.top_surjective (degreeFourTopDerangement block hs))

theorem degreeFourAmbientDerangement_top
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    let S := initialState hTraceyPerm block
    (S.rho (degreeFourAmbientDerangement block hTraceyPerm hs)).right =
      degreeFourTopDerangement block hs := by
  let S := initialState hTraceyPerm block
  exact Classical.choose_spec
    (S.top_surjective (degreeFourTopDerangement block hs))

/-- The actual subgroup used in Tracey's soluble-orbit formula. -/
abbrev degreeFourTraceySubgroup
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    Subgroup (preE7NonPairAction w U) :=
  degreeFourTernaryPreimage block P ⊔
    Subgroup.zpowers
      (degreeFourAmbientDerangement block hTraceyPerm hs)

/-- The ternary-core preimage, viewed inside the actual Tracey subgroup. -/
abbrev degreeFourTraceyCoreSubgroup
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs) :=
  (degreeFourTernaryPreimage block P).subgroupOf
    (degreeFourTraceySubgroup block P hTraceyPerm hs)

instance degreeFourTraceyCoreSubgroup_normal
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).Normal :=
  Subgroup.normal_subgroupOf

/-- The lifted derangement as an element of the Tracey subgroup. -/
noncomputable def degreeFourTraceyDerangement
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    degreeFourTraceySubgroup block P hTraceyPerm hs :=
  ⟨degreeFourAmbientDerangement block hTraceyPerm hs,
    (show Subgroup.zpowers
        (degreeFourAmbientDerangement block hTraceyPerm hs) ≤
          degreeFourTernaryPreimage block P ⊔ Subgroup.zpowers
            (degreeFourAmbientDerangement block hTraceyPerm hs) from
      le_sup_right) (Subgroup.mem_zpowers _)⟩

theorem degreeFourTraceyCore_sup_derangement_eq_top
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    degreeFourTraceyCoreSubgroup block P hTraceyPerm hs ⊔
        Subgroup.zpowers
          (degreeFourTraceyDerangement block P hTraceyPerm hs) = ⊤ := by
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  let B := degreeFourTernaryPreimage block P
  let z := degreeFourAmbientDerangement block hTraceyPerm hs
  rw [← (Subgroup.map_injective N.subtype_injective).eq_iff]
  rw [Subgroup.map_sup, MonoidHom.map_zpowers,
    ← MonoidHom.range_eq_map, N.range_subtype]
  change
    (B.subgroupOf N).map N.subtype ⊔ Subgroup.zpowers z = B ⊔ Subgroup.zpowers z
  rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left]

/-- Hence the quotient of the actual Tracey subgroup by the ternary-core
preimage is cyclic, with no classification input. -/
noncomputable instance degreeFourTracey_quotient_core_isCyclic
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    IsCyclic
      (degreeFourTraceySubgroup block P hTraceyPerm hs ⧸
        degreeFourTraceyCoreSubgroup block P hTraceyPerm hs) :=
  isCyclic_quotient_of_sup_zpowers_eq_top
    (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs)
    (degreeFourTraceyDerangement block P hTraceyPerm hs)
    (degreeFourTraceyCore_sup_derangement_eq_top
      block P hTraceyPerm hs)

/-- Every Tracey-subgroup orbit on blocks contains at least two points,
because it contains the chosen derangement. -/
theorem degreeFourTracey_orbit_card_two_le
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points)
    (o : MulAction.orbitRel.Quotient
      (degreeFourTraceySubgroup block P hTraceyPerm hs) block.Points) :
    2 ≤ Nat.card o.orbit := by
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  let zN := degreeFourTraceyDerangement block P hTraceyPerm hs
  have hmove : zN • o.out ≠ o.out := by
    intro hfix
    have hfix' :
        ((initialState hTraceyPerm block).rho
          (degreeFourAmbientDerangement block hTraceyPerm hs)).right •
            o.out = o.out := by
      simpa only [zN, N, degreeFourTraceyDerangement,
        Subgroup.smul_def, initialState, ambientEmbedding,
        ActualBlockWreathEmbedding.embedding] using hfix
    rw [degreeFourAmbientDerangement_top block hTraceyPerm hs] at hfix'
    have hmem : o.out ∈ MulAction.fixedBy block.Points
        (degreeFourTopDerangement block hs) := hfix'
    rw [degreeFourTopDerangement_fixedBy block hs] at hmem
    exact hmem
  have hout_mem : o.out ∈ o.orbit :=
    MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' o)
  have hzN_mem : zN • o.out ∈ o.orbit := by
    rw [o.orbit_eq_orbit_out Quotient.out_eq']
    exact MulAction.mem_orbit o.out zN
  rw [Nat.card_coe_set_eq]
  calc
    2 = ({o.out, zN • o.out} : Set block.Points).ncard :=
      (Set.ncard_pair hmove.symm).symm
    _ ≤ o.orbit.ncard := Set.ncard_le_ncard
      (Set.pair_subset hout_mem hzN_mem)

/-! ## Solubility of the displayed subgroup -/

/-- The full ternary-core preimage is soluble: it is an extension of the
abelian binary translation intersection by the abelian correlated ternary
core. -/
theorem degreeFourTernaryPreimage_isSolvable
    (hr : Nat.card block.Fibre = 4) :
    IsSolvable (degreeFourTernaryPreimage block P) := by
  let E0 := E block P
  let B := degreeFourTernaryPreimage block P
  let D0 := degreeFourTernaryCore block P
  let q : preE7NonPairAction w U →*
      DegreeFourComplementQuotient block P := QuotientGroup.mk' E0
  let f : E0 →* B := Subgroup.inclusion
    (degreeFour_translation_le_ternaryPreimage block P)
  let g : B →* D0 := {
    toFun := fun b ↦ ⟨q b.1, by
      change q b.1 ∈ degreeFourTernaryCore block P
      rw [← degreeFour_ternaryPreimage_map_eq_core block P]
      exact ⟨b.1, b.2, rfl⟩⟩
    map_one' := by ext; simp [q]
    map_mul' := by intro x y; ext; simp [q] }
  letI : IsSolvable E0 := isSolvable_of_comm (fun x y ↦
    (degreeFive_translation_commute block P x y).eq)
  letI : IsSolvable D0 := isSolvable_of_comm (fun x y ↦
    (degreeFourTernaryCore_commute block P hr x y).eq)
  apply solvable_of_ker_le_range f g
  intro b hb
  have hbE : b.1 ∈ E0 := by
    apply (QuotientGroup.eq_one_iff b.1).mp
    exact congrArg Subtype.val hb
  exact ⟨⟨b.1, hbE⟩, Subtype.ext rfl⟩

/-- The whole ternary-core preimage fixes every displayed block. -/
theorem degreeFourTernaryPreimage_le_blockKernelPreimage :
    degreeFourTernaryPreimage block P ≤
      degreeFiveBlockKernelPreimage block P := by
  intro b hb
  change QuotientGroup.mk' (E block P) b ∈
    degreeFiveQuotientBlockKernel block P
  exact degreeFourTernaryCore_le_blockKernel block P hb

/-- The actual Tracey subgroup is soluble: its normal core-preimage is
soluble and its displayed quotient is cyclic. -/
theorem degreeFourTraceySubgroup_isSolvable
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points) :
    IsSolvable (degreeFourTraceySubgroup block P hTraceyPerm hs) := by
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  let B := degreeFourTernaryPreimage block P
  let BN := degreeFourTraceyCoreSubgroup block P hTraceyPerm hs
  letI : IsSolvable B := degreeFourTernaryPreimage_isSolvable block P hr
  let toB : BN →* B := {
    toFun := fun b ↦ ⟨b.1.1, b.2⟩
    map_one' := by ext; rfl
    map_mul' := by intro x y; ext; rfl }
  have htoB : Function.Injective toB := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B ↦ (z.1 : preE7NonPairAction w U)) hxy
  letI : IsSolvable BN := solvable_of_solvable_injective htoB
  letI : (degreeFourTraceyCoreSubgroup
      block P hTraceyPerm hs).Normal :=
    Subgroup.normal_subgroupOf
  let Q := degreeFourTraceySubgroup block P hTraceyPerm hs ⧸
    degreeFourTraceyCoreSubgroup block P hTraceyPerm hs
  letI : IsCyclic Q :=
    degreeFourTracey_quotient_core_isCyclic block P hTraceyPerm hs
  letI : CommGroup Q := IsCyclic.commGroup
  letI : IsSolvable Q := CommGroup.isSolvable
  apply solvable_of_ker_le_range
    (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).subtype
    (QuotientGroup.mk'
      (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs))
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

/-! ## The actual odd Hall subgroup -/

/-- The binary translation intersection, viewed in the actual Tracey
subgroup. -/
abbrev degreeFourTraceyTranslationSubgroup
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs) :=
  (E block P).subgroupOf (degreeFourTraceySubgroup block P hTraceyPerm hs)

instance degreeFourTraceyTranslationSubgroup_normal
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    (degreeFourTraceyTranslationSubgroup block P hTraceyPerm hs).Normal :=
  Subgroup.normal_subgroupOf

theorem degreeFourTraceyTranslation_le_core
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    degreeFourTraceyTranslationSubgroup block P hTraceyPerm hs ≤
      degreeFourTraceyCoreSubgroup block P hTraceyPerm hs := by
  intro e he
  exact degreeFour_translation_le_ternaryPreimage block P he

/-- The binary translation intersection really is a finite two-group.  The
proof uses its literal exponent-two law, rather than a catalogue entry. -/
theorem degreeFourTraceyTranslation_card_two_pow
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points) :
    ∃ a : ℕ,
      Nat.card (degreeFourTraceyTranslationSubgroup
        block P hTraceyPerm hs) = 2 ^ a := by
  apply IsPGroup.exists_card_eq
  intro e
  refine ⟨1, ?_⟩
  change e ^ 2 = 1
  apply Subtype.ext
  apply Subtype.ext
  change (e.1.1 : preE7NonPairAction w U) ^ 2 = 1
  simpa using congrArg
    (fun x : E block P ↦ (x : preE7NonPairAction w U))
    (degreeFour_translation_pow_two block P hr ⟨e.1.1, e.2⟩)

/-- The odd layer inside `N/E` has exactly the order of the literal
correlated ternary core.  This is relative-index transport through two
actual subgroup inclusions; no product decomposition of the core is used. -/
theorem degreeFourTraceyOddLayer_card_eq_core
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hs : 2 ≤ Nat.card block.Points) :
    Nat.card
        ((degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs))) =
      Nat.card (degreeFourTernaryCore block P) := by
  let N := degreeFourTraceySubgroup block P hTraceyPerm hs
  let E0 := E block P
  let B := degreeFourTernaryPreimage block P
  let EN := degreeFourTraceyTranslationSubgroup block P hTraceyPerm hs
  let BN := degreeFourTraceyCoreSubgroup block P hTraceyPerm hs
  calc
    Nat.card (BN.map (QuotientGroup.mk' EN)) = EN.relIndex BN := by
      rw [← Subgroup.relIndex_ker (f := QuotientGroup.mk' EN) (K := BN),
        QuotientGroup.ker_mk']
    _ = E0.relIndex B := by
      exact Subgroup.relIndex_subgroupOf (H := E0) (K := B)
        (L := N) le_sup_left
    _ = Nat.card (B.map (QuotientGroup.mk' E0)) := by
      simpa only [QuotientGroup.ker_mk'] using
        (Subgroup.relIndex_ker B (QuotientGroup.mk' E0))
    _ = Nat.card (degreeFourTernaryCore block P) := by
      rw [degreeFour_ternaryPreimage_map_eq_core block P]

/-- Hence the actual odd layer has odd order. -/
theorem degreeFourTraceyOddLayer_card_odd
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points) :
    ¬ 2 ∣ Nat.card
        ((degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).map
          (QuotientGroup.mk'
            (degreeFourTraceyTranslationSubgroup
              block P hTraceyPerm hs))) := by
  rw [degreeFourTraceyOddLayer_card_eq_core block P hTraceyPerm hs]
  let C := degreeFourTernaryCoreChart block P hr
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod C.p) C.V := C.module
  letI : Fact C.p.Prime := C.primeFact
  letI : FiniteDimensional (ZMod C.p) C.V := C.finiteDimensional
  have hcard : Nat.card (degreeFourTernaryCore block P) =
      C.p ^ Module.finrank (ZMod C.p) C.V := by
    calc
      Nat.card (degreeFourTernaryCore block P) = Nat.card C.V :=
        Nat.card_congr C.equiv.toEquiv
      _ = Nat.card (ZMod C.p) ^ Module.finrank (ZMod C.p) C.V :=
        Module.natCard_eq_pow_finrank
      _ = C.p ^ Module.finrank (ZMod C.p) C.V := by rw [Nat.card_zmod]
  rw [hcard]
  intro hdiv
  have : 2 ∣ C.p := Nat.prime_two.dvd_of_dvd_pow hdiv
  change 2 ∣ 3 at this
  norm_num at this

/-- The Schur--Zassenhaus construction applied to the literal binary and
ternary layers produces the actual `2`-complement required by Tracey's
theorem.  Its image modulo the binary layer still contains the whole
correlated ternary core. -/
theorem exists_degreeFourTraceyTwoComplement
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hs : 2 ≤ Nat.card block.Points) :
    ∃ P₂ : Subgroup (degreeFourTraceySubgroup block P hTraceyPerm hs),
      IsTwoComplement P₂ ∧
        (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs).map
            (QuotientGroup.mk'
              (degreeFourTraceyTranslationSubgroup
                block P hTraceyPerm hs)) ≤
          P₂.map
            (QuotientGroup.mk'
              (degreeFourTraceyTranslationSubgroup
                block P hTraceyPerm hs)) := by
  exact exists_isTwoComplement_mapping_over_normalLayer
    (degreeFourTraceyTranslationSubgroup block P hTraceyPerm hs)
    (degreeFourTraceyCoreSubgroup block P hTraceyPerm hs)
    (degreeFourTraceyTranslation_le_core block P hTraceyPerm hs)
    (degreeFourTraceyTranslation_card_two_pow block P hTraceyPerm hr hs)
    (degreeFourTraceyOddLayer_card_odd block P hTraceyPerm hr hs)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
