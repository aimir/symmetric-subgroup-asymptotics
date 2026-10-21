import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightActualConsumerFacts
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentSourceAssemblyBinarySmallReduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallCatalogueCapacityBinarySmallReduced

/-! Degree8-only actual local consumer. The proved degree8 locator supplies
its exact orders directly; no degree16 locator or bundled small package is
requested. The original action, correlated kernel and normal axes remain. -/
set_option autoImplicit false

noncomputable section

open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffineImprimitiveBlockTransfer

namespace DegreeEightActual

namespace BinaryAffineExceptionalShape

end BinaryAffineExceptionalShape

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private theorem degreeEight_seven_dvd_of_solubleRow
    (r : SmallAffineCatalogueRow) (hd : r.degree = 8)
    (hs : r.nonsoluble = false) : 7 ∣ r.complementOrder := by
  rcases r with ⟨i⟩ | ⟨i⟩ | ⟨i⟩ <;>
    fin_cases i <;>
    simp_all [SmallAffineCatalogueRow.degree,
      SmallAffineCatalogueRow.complementOrder,
      SmallAffineCatalogueRow.nonsoluble]

theorem binaryAffineExceptional_locate_soluble_complement
    (hdegreeEight : Nat.card block.Fibre=8)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    ∃ r : SmallAffineCatalogueRow,
      r.degree = Nat.card block.Fibre ∧ r.nonsoluble = false ∧
      Nat.card (P.complement (origin block)) = r.complementOrder := by
  exact PrimitiveAffineDegreeEightActualConsumerFacts.locate_soluble
    block.component_preprimitive P (origin block) hdegreeEight hsoluble

theorem binaryAffineExceptional_local_order_obstruction
    (hdegreeEight : Nat.card block.Fibre=8)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    (Nat.card block.Fibre = 8 ∧
        7 ∣ Nat.card (P.complement (origin block))) ∨
      (Nat.card block.Fibre = 16 ∧
        ¬ Nat.card (P.complement (origin block)) ∣ 6) := by
  obtain ⟨r, hrDegree, hrSoluble, hrOrder⟩ :=
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.binaryAffineExceptional_locate_soluble_complement
      block P hdegreeEight shape hsoluble
  cases shape with
  | degreeEight hr _hs =>
    left
    refine ⟨hr, ?_⟩
    rw [hrOrder]
    exact degreeEight_seven_dvd_of_solubleRow r
      (hrDegree.trans hr) hrSoluble
  | degreeSixteen hr _hs => omega

theorem binaryAffineLinearBlockKernelCoordinate_range_ne_bot
    (hdegreeEight : Nat.card block.Fibre=8)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i : block.Points) :
    (binaryAffineLinearBlockKernelCoordinate block P i).range ≠ ⊥ := by
  intro hzero
  have hK : binaryAffineLinearBlockKernel block P = ⊥ :=
    binaryAffineLinearBlockKernel_eq_bot_of_coordinate_range_eq_bot
      block P i hzero
  have hlocal_stabilizer : Nat.card (LocalQuotient block P) ∣
      Nat.card (binaryAffineQuotientTopStabilizer block P i) :=
    Subgroup.card_dvd_of_surjective
      (binaryAffineStabilizerComponent block P i)
      (binaryAffineStabilizerComponent_surjective block P i)
  have hstabilizer_top :
      Nat.card (binaryAffineQuotientTopStabilizer block P i) ∣
        Nat.card (MulAction.stabilizer block.Top i) :=
    Subgroup.card_dvd_of_injective
      (binaryAffineStabilizerTopMap block P i)
      (binaryAffineStabilizerTopMap_injective_of_kernel_eq_bot
        block P i hK)
  have hlocal_factorial : Nat.card (LocalQuotient block P) ∣
      (Nat.card block.Points - 1).factorial :=
    hlocal_stabilizer.trans (hstabilizer_top.trans
      (binaryAffineTopStabilizer_card_dvd_factorial_pred block i))
  have hlocalCard : Nat.card (LocalQuotient block P) =
      Nat.card (P.complement (origin block)) :=
    localQuotient_card_eq_complement block P
  rcases _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.binaryAffineExceptional_local_order_obstruction
      block P hdegreeEight shape hsoluble with h8 | h16
  · have h7 : 7 ∣ Nat.card (LocalQuotient block P) := by
      rw [hlocalCard]
      exact h8.2
    have hbad : 7 ∣ (Nat.card block.Points - 1).factorial :=
      h7.trans hlocal_factorial
    cases shape with
    | degreeEight _ hs =>
      rcases hs with hs | hs | hs <;> rw [hs] at hbad <;> norm_num at hbad
    | degreeSixteen hr _ => exact (by omega)
  · have hnot : ¬ Nat.card (LocalQuotient block P) ∣ 6 := by
      rw [hlocalCard]
      exact h16.2
    apply hnot
    refine hlocal_factorial.trans ?_
    cases shape with
    | degreeEight hr _ => exact (by omega)
    | degreeSixteen _ hs =>
      rcases hs with hs | hs <;> rw [hs] <;> norm_num

theorem binaryAffineExceptional_complement_order_divisor
    (hdegreeEight : Nat.card block.Fibre=8)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hsoluble : IsSolvable (P.complement (origin block))) :
    (Nat.card block.Fibre = 8 ∧
        Nat.card (P.complement (origin block)) ∣ 21) ∨
      (Nat.card block.Fibre = 16 ∧
        Nat.card (P.complement (origin block)) ∣ 360) := by
  cases shape with
  | degreeEight hr _hs =>
      exact Or.inl ⟨hr,PrimitiveAffineDegreeEightActualConsumerFacts.soluble_card_dvd_twentyOne
        block.component_preprimitive P (origin block) hr hsoluble⟩
  | degreeSixteen hr _hs => omega

theorem degreeEight_seven_dvd_coordinate_range_card
    (hdegreeEight : Nat.card block.Fibre=8)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i : block.Points) :
    7 ∣ Nat.card
      (binaryAffineLinearBlockKernelCoordinate block P i).range := by
  let D := (binaryAffineLinearBlockKernelCoordinate block P i).range
  letI : D.Normal :=
    binaryAffineLinearBlockKernelCoordinate_range_normal block P i
  have hDne : D ≠ ⊥ :=
    _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.binaryAffineLinearBlockKernelCoordinate_range_ne_bot
      block P hdegreeEight shape hsoluble i
  have hlocal : Nat.card (LocalQuotient block P) ∣ 21 := by
    rw [localQuotient_card_eq_complement block P]
    rcases _root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.binaryAffineExceptional_complement_order_divisor
      block P hdegreeEight shape hsoluble with h8 | h16
    · exact h8.2
    · exact False.elim (by omega)
  have hDdiv : Nat.card D ∣ 21 :=
    (Subgroup.card_dvd_of_injective D.subtype Subtype.val_injective).trans
      hlocal
  by_contra h7
  have hcop : Nat.Coprime (Nat.card D) 7 :=
    (((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd).2 h7).symm
  have hDdiv3 : Nat.card D ∣ 3 := by
    exact hcop.dvd_mul_right.mp (by simpa only [show 21 = 3 * 7 by norm_num]
      using hDdiv)
  have hDone : Nat.card D ≠ 1 := by
    intro hone
    letI : Subsingleton D := (Nat.card_eq_one_iff_unique.mp hone).1
    apply hDne
    rw [eq_bot_iff]
    intro d hd
    exact congrArg Subtype.val (Subsingleton.elim ⟨d, hd⟩ 1)
  have hDcard : Nat.card D = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hDdiv3).resolve_left hDone
  have hDp : IsPGroup 3 D :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hDcard)
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  let ρD := (binaryAffineLocalLinearRepresentation block P).ρ.comp D.subtype
  letI : MulAction D C.V :=
    { smul := fun d v => ρD d v
      one_smul := by intro v; change ρD 1 v = v; simp
      mul_smul := by
        intro a b v
        change ρD (a * b) v = ρD a (ρD b v)
        rw [map_mul]
        rfl }
  have hfixedCard : Nat.card (MulAction.fixedPoints D C.V) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨?_, ⟨⟨0, by intro d; exact map_zero (ρD d)⟩⟩⟩
    constructor
    intro x y
    apply Subtype.ext
    have hxInv : x.1 ∈ Representation.invariants ρD := x.2
    have hyInv : y.1 ∈ Representation.invariants ρD := y.2
    rw [binaryAffineLocalNormal_invariants_eq_bot block P D hDne] at hxInv
    rw [binaryAffineLocalNormal_invariants_eq_bot block P D hDne] at hyInv
    rw [(Submodule.mem_bot (R := ZMod P.p)).mp hxInv,
      (Submodule.mem_bot (R := ZMod P.p)).mp hyInv]
  have hVcard : Nat.card C.V = 8 := by
    calc
      Nat.card C.V = Nat.card (Multiplicative C.V) := rfl
      _ = Nat.card P.V := Nat.card_congr C.equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
      _ = 8 := hr
  have hmod := hDp.card_modEq_card_fixedPoints C.V
  rw [hVcard, hfixedCard] at hmod
  exact (by norm_num : ¬ (8 ≡ 1 [MOD 3])) hmod

theorem degreeEight_seven_dvd_linearBlockKernel_card
    (hdegreeEight : Nat.card block.Fibre=8)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i : block.Points) :
    7 ∣ Nat.card (binaryAffineLinearBlockKernel block P) := by
  exact (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.degreeEight_seven_dvd_coordinate_range_card
    block P hdegreeEight shape hr hsoluble i).trans
      (Subgroup.card_dvd_of_surjective
        (binaryAffineLinearBlockKernelCoordinate block P i).rangeRestrict
        (binaryAffineLinearBlockKernelCoordinate block P i).rangeRestrict_surjective)

private theorem eight_le_card_of_seven_dvd_faithful_representation
    {p : ℕ} [Fact p.Prime]
    {K W : Type} [Group K] [Finite K]
    [AddCommGroup W] [Module (ZMod p) W]
    [FiniteDimensional (ZMod p) W] [Finite W]
    (hp : p = 2) (ρ : Representation (ZMod p) K W)
    (hfaithful : Function.Injective ρ)
    (hseven : 7 ∣ Nat.card K) :
    8 ≤ Nat.card W := by
  subst p
  let d := Module.finrank (ZMod 2) W
  have hWcard : Nat.card W = 2 ^ d := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  letI : Finite (Module.End (ZMod 2) W) :=
    Finite.of_injective
      (fun u : Module.End (ZMod 2) W => (u : W → W))
      LinearMap.coe_injective
  have hKleGL : Nat.card K ≤ Nat.card (Module.End (ZMod 2) W)ˣ := by
    exact Nat.card_le_card_of_injective ρ.toHomUnits (by
      intro x y hxy
      apply hfaithful
      exact congrArg Units.val hxy)
  have hsevenK : 7 ≤ Nat.card K :=
    Nat.le_of_dvd (Nat.card_pos (α := K)) hseven
  by_contra hsmall
  have hd : d ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ d := by omega
    have hpow : 2 ^ 3 ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by norm_num) hthree
    rw [← hWcard] at hpow
    omega
  have hGLle : Nat.card (Module.End (ZMod 2) W)ˣ ≤ 6 := by
    let basis : Module.Basis
        (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W :=
      Module.finBasisOfFinrankEq (ZMod 2) W rfl
    rw [← Nat.card_congr
      (Matrix.GeneralLinearGroup.toLin' basis).toEquiv,
      Matrix.card_GL_field]
    simp only [ZMod.card]
    have hcases : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · have hdim : Module.finrank (ZMod 2) W = 0 := by simpa [d] using hzero
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 1 := by simpa [d] using hone
      rw [hdim]
      norm_num
    · have hdim : Module.finrank (ZMod 2) W = 2 := by simpa [d] using htwo
      rw [hdim]
      norm_num
  omega

theorem degreeEight_translationMinimal_card_le_of_clifford
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hdegreeEight : Nat.card block.Fibre=8)
    (shape : BinaryAffineExceptionalShape
      (Nat.card block.Fibre) (Nat.card block.Points))
    (hr : Nat.card block.Fibre = 8)
    (hsoluble : IsSolvable (P.complement (origin block)))
    (i₀ : block.Points)
    (N : BinaryAffineLiteralNormalAxis (preE7NonPairAction w U))
    (hretained : ¬ E block P ≤ N.1)
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hM : IsMinimalNormalSubgroup M)
    (hME : M ≤ binaryAffineTranslationImage block P N) :
    8 ≤ Nat.card M := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  let N' : Subgroup S.A := N.1
  letI : N'.Normal := by
    dsimp only [N']
    exact N.2
  letI : Finite
      (ActualWreathAffineCapacity.E S (localMap block P) C).V :=
    Finite.of_injective
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block P) C.equiv.symm).subtype
      (PermutationalWreathProduct.Compression.ElementarySubmodule
        (p := C.p) S.rho (localMap block P) C.equiv.symm).subtype_injective
  letI : Finite
      (ActualWreathAffineCapacity.E S
        (localMap block P) C).quotientRepresentation :=
    inferInstanceAs (Finite
      (ActualWreathAffineCapacity.E S (localMap block P) C).V)
  let normalSpace :=
    (ActualWreathAffineCapacity.originalChart S (localMap block P) C).normalSpace
      (ActualWreathAffineCapacity.pi S (localMap block P))
      (ActualWreathAffineCapacity.E S
        (localMap block P) C).quotientRepresentation N'
  letI : Finite
      (CliffordHomogeneousRestriction.sectionTopRepresentation
        S (localMap block P) C N') :=
    Finite.of_surjective normalSpace.mkQ normalSpace.mkQ_surjective
  let M' : Subgroup (S.A ⧸ N') := M
  letI : M'.Normal := by
    dsimp only [M']
    exact hM.1
  let W : Subrepresentation
      (CliffordHomogeneousRestriction.sectionTopRepresentation
        S (localMap block P) C N').ρ :=
    CliffordHomogeneousRestriction.retainedNormalConstituent
      S (localMap block P) C N' M'
  -- `Subrepresentation` is only a `SetLike`; its coercion to a type does
  -- not carry the inherited module instances.  The representation itself
  -- lives on the carrier of `toSubmodule`, so keep that literal carrier in
  -- the finite linear-group argument below.
  letI : Module (ZMod C.p) W.toSubmodule := W.toSubmodule.module
  letI : FiniteDimensional (ZMod C.p) W.toSubmodule :=
    FiniteDimensional.finiteDimensional_submodule W.toSubmodule
  letI : Finite W.toSubmodule :=
    Finite.of_injective W.toSubmodule.subtype
      W.toSubmodule.subtype_injective
  have hME' : M' ≤ CliffordHomogeneousRestriction.retainedElementaryImage
      S (localMap block P) N' := by
    simpa only [M', N', S,
      CliffordHomogeneousRestriction.retainedElementaryImage,
      CliffordHomogeneousRestriction.elementaryKernel,
      ActualWreathAffineCapacity.K, initialState] using hME
  have hMne : M' ≠ ⊥ := by
    simpa only [M'] using hM.2.1
  have hW : W ≠ ⊥ :=
    CliffordHomogeneousRestriction.retainedNormalConstituent_ne_bot
      S (localMap block P) C N' M' hME' hMne
  have hfaithful : Function.Injective
      (CliffordHomogeneousRestriction.constituentLinearKernelRepresentation
        S (localMap block P) C N' W).ρ :=
    hClifford.faithfulNonzeroConstituent
      S (localMap block P) (localMap_surjective block P) C
      (by
        rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
        exact binaryAffineLocalLinearRepresentation_irreducible block P)
      (by
        rw [cliffordLocalRepresentation_rho_eq block P hTraceyPerm]
        exact binaryAffineLocalLinearRepresentation_injective block P)
      (by
        intro i
        simpa only [S, CliffordHomogeneousRestriction.linearCoordinate,
          CliffordHomogeneousRestriction.linearBlockKernel, initialState,
          quotientEmbedding] using
            (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.binaryAffineLinearBlockKernelCoordinate_range_ne_bot
              block P hdegreeEight shape hsoluble i))
      N' (by
        simpa only [N', S, C,
          CliffordHomogeneousRestriction.elementaryKernel,
          ActualWreathAffineCapacity.K, initialState] using hretained)
      W hW
  have h7K : 7 ∣ Nat.card
      (CliffordHomogeneousRestriction.linearBlockKernel S (localMap block P)) := by
    simpa only [S, CliffordHomogeneousRestriction.linearBlockKernel,
      initialState, quotientEmbedding] using
        (_root_.SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightActual.degreeEight_seven_dvd_linearBlockKernel_card
          block P hdegreeEight shape hr hsoluble i₀)
  have hcardWM : Nat.card W ≤ Nat.card M := by
    simpa only [M'] using
      (CliffordHomogeneousRestriction.natCard_retainedNormalConstituent_le
        S (localMap block P) C N' M' hME')
  have hp : C.p = 2 := by
    simpa only [C, localTranslationChart] using
      (degreeEight_translationDimension block P hr).1
  let σ :=
    W.toRepresentation.comp
      (CliffordHomogeneousRestriction.linearKernelToSectionTop
        S (localMap block P) N')
  have hσ : Function.Injective σ := by
    simpa only [σ,
      CliffordHomogeneousRestriction.constituentLinearKernelRepresentation]
      using hfaithful
  have hVcard : 8 ≤ Nat.card W.toSubmodule :=
    eight_le_card_of_seven_dvd_faithful_representation hp σ hσ h7K
  exact hVcard.trans (by simpa only using hcardWM)

end DegreeEightActual
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
