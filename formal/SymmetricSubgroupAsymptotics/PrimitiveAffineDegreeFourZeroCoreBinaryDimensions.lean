import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreBinarySection
import SymmetricSubgroupAsymptotics.BinaryCharacterProducts
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank

/-!
# Dimension bounds for the binary socle filtration

The translation term is the literal intersection of the selected elementary
binary socle with the retained correlated translation image.  Its module
cardinality is therefore at most the cardinality of that translation image,
which is at most `4^s`.  This gives the required `2s`-dimensional bound
without replacing the correlated translation group by a coordinate product.
-/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Characters of an elementary `p`-module are its linear dual.  The
binary theorem used elsewhere is the specialization `p = 2`; keeping the
prime native here avoids dependent transports through the retained chart. -/
private def primeVectorCharactersEquiv
    (p : ℕ) [Fact p.Prime]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] :
    PrimeCharacters p (Multiplicative V) ≃ₗ[ZMod p]
      Module.Dual (ZMod p) V where
  toFun χ :=
    ({ toFun := fun v ↦ χ (Additive.ofMul (Multiplicative.ofAdd v))
       map_zero' := χ.map_zero
       map_add' := χ.map_add } : V →+ ZMod p).toZModLinearMap p
  invFun f :=
    { toFun := fun v ↦ f v.toMul.toAdd
      map_zero' := f.map_zero
      map_add' := f.map_add }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem primeCharacterRank_multiplicative
    (p : ℕ) [Fact p.Prime]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V] :
    Module.finrank (ZMod p) (PrimeCharacters p (Multiplicative V)) =
      Module.finrank (ZMod p) V := by
  rw [(primeVectorCharactersEquiv p V).finrank_eq,
    Subspace.dual_finrank_eq]

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The translation term in the noncentral binary socle filtration has
dimension at most twice the number of blocks. -/
theorem degreeFourBinaryTargetSection_finrank_le_twice_blocks
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Module.finrank (ZMod (DegreeFourBinarySocleChart block P N).p)
        (DegreeFourBinaryTargetSection block P N).toSubmodule ≤
      2 * Nat.card block.Points := by
  let A := DegreeFourBinarySocle block P N
  let C := DegreeFourBinarySocleChart block P N
  let H := DegreeFourBinaryTranslationIntersection block P N
  let T := DegreeFourBinaryTargetSection block P N
  letI : Fact C.p.Prime := C.primeFact
  letI : FiniteDimensional (ZMod C.p) C.quotientRepresentation :=
    C.finiteDimensional
  letI : Module (ZMod C.p) T.toSubmodule := T.toSubmodule.module
  letI : FiniteDimensional (ZMod C.p) T.toSubmodule :=
    FiniteDimensional.finiteDimensional_submodule T.toSubmodule
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  have hCp : C.p = P.p := by
    dsimp only [C, DegreeFourBinarySocleChart,
      selectedPrimeSoclePartElementaryChart]
  have hcardT : Nat.card T.toSubmodule =
      C.p ^ Module.finrank (ZMod C.p) T.toSubmodule := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]
  have hHA : H ⊓ A = H := inf_eq_left.mpr inf_le_left
  let targetEquiv : Multiplicative T.toSubmodule ≃* H := by
    simpa only [T, H, DegreeFourBinaryTargetSection,
      DegreeFourBinaryTranslationIntersection] using
      ((degreeFourBinaryTargetIntersectionEquiv block P N).symm.trans
        (MulEquiv.subgroupCongr hHA))
  have hcardTH : Nat.card T.toSubmodule = Nat.card H := by
    exact Nat.card_congr
      (Multiplicative.ofAdd.trans targetEquiv.toEquiv)
  have hC2 : C.p = 2 := hCp.trans hp
  have hpow : 2 ^ Module.finrank (ZMod C.p) T.toSubmodule ≤
      2 ^ (2 * Nat.card block.Points) := by
    calc
      2 ^ Module.finrank (ZMod C.p) T.toSubmodule =
          C.p ^ Module.finrank (ZMod C.p) T.toSubmodule := by
        exact (congrArg
          (fun q : ℕ ↦ q ^ Module.finrank (ZMod C.p) T.toSubmodule)
          hC2).symm
      _ = Nat.card T.toSubmodule := hcardT.symm
      _ = Nat.card H := hcardTH
      _ ≤ Nat.card (degreeFourTranslationImage block P N) :=
        Subgroup.card_le_of_le inf_le_right
      _ ≤ 4 ^ Nat.card block.Points :=
        degreeFourTranslationImage_card_le block P hr N
      _ = 2 ^ (2 * Nat.card block.Points) := by
        rw [show 4 = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow

/-- The complementary binary socle quotient embeds in the literal retained
block top.  Consequently its dimension is at most the binary sectional rank
of that top, namely half the number of blocks.  The proof retains the actual
intersection with the correlated translation image as the quotient kernel. -/
theorem degreeFourBinaryTopQuotient_twice_finrank_le_blocks
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    2 * Module.finrank (ZMod (DegreeFourBinarySocleChart block P N).p)
        ((DegreeFourBinarySocleChart block P N).quotientRepresentation ⧸
          (DegreeFourBinaryTargetSection block P N).toSubmodule) ≤
      Nat.card block.Points := by
  let Q := DegreeFourRetainedQuotient N
  let A := DegreeFourBinarySocle block P N
  let C := DegreeFourBinarySocleChart block P N
  let sigma := C.quotientRepresentation.ρ
  let H := DegreeFourBinaryTranslationIntersection block P N
  let T := DegreeFourBinaryTargetSection block P N
  let Vbar := degreeFourTranslationImage block P N
  letI : Fact C.p.Prime := C.primeFact
  letI : FiniteDimensional (ZMod C.p) C.quotientRepresentation :=
    C.finiteDimensional
  letI : Module (ZMod C.p)[Q ⧸ A] sigma.asModule :=
    Representation.instModuleMonoidAlgebraAsModule sigma
  letI : IsScalarTower (ZMod C.p) (ZMod C.p)[Q ⧸ A] sigma.asModule :=
    inferInstanceAs
      (IsScalarTower (ZMod C.p) (ZMod C.p)[Q ⧸ A]
        (Representation.asModule sigma))
  let proj : Multiplicative sigma.asModule →*
      Multiplicative (sigma.asModule ⧸ T.toSubmodule) :=
    T.toSubmodule.mkQ.toAddMonoidHom.toMultiplicative
  have hproj : Function.Surjective proj := by
    intro z
    obtain ⟨v, hv⟩ := T.toSubmodule.mkQ_surjective z.toAdd
    exact ⟨Multiplicative.ofAdd v, congrArg Multiplicative.ofAdd hv⟩
  let topMap : Q →* Q ⧸ Vbar := QuotientGroup.mk' Vbar
  let f : Multiplicative sigma.asModule →* Q ⧸ Vbar :=
    topMap.comp (A.subtype.comp C.equiv.symm.toMonoidHom)
  have hker : proj.ker = f.ker := by
    ext v
    change T.toSubmodule.mkQ v.toAdd = 0 ↔
      QuotientGroup.mk' Vbar (C.equiv.symm v).1 = 1
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    let a : A := C.equiv.symm v
    have ha : C.equiv a = v := C.equiv.apply_symm_apply v
    have hmem := elementaryIntersectionModule_mem_iff A C H a
    rw [ha] at hmem
    have hq := QuotientGroup.eq_one_iff (N := Vbar) (a.1 : Q)
    exact (hmem.trans (and_iff_right a.2)).trans hq.symm
  have hkerRange : proj.ker = f.rangeRestrict.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using hker
  let e : Multiplicative (sigma.asModule ⧸ T.toSubmodule) ≃* f.range :=
    (QuotientGroup.liftEquiv proj.ker hproj rfl).symm.trans
      (QuotientGroup.liftEquiv proj.ker
        f.rangeRestrict_surjective hkerRange)
  let embedding : Multiplicative (sigma.asModule ⧸ T.toSubmodule) →*
      Q ⧸ Vbar := f.range.subtype.comp e.toMonoidHom
  have hembedding : Function.Injective embedding :=
    Subtype.val_injective.comp e.injective
  have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
  have hCp : C.p = P.p := by
    dsimp only [C, DegreeFourBinarySocleChart,
      selectedPrimeSoclePartElementaryChart]
  have hC2 : C.p = 2 := hCp.trans hp
  let G := preE7NonPairAction w U
  let L : Subgroup G := degreeFiveBlockKernelPreimage block P ⊔ N.1
  have hmap : L.map (QuotientGroup.mk' N.1) =
      degreeFiveRetainedBlockKernel block P N := by
    dsimp only [L, degreeFiveRetainedBlockKernel]
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  have hretained : degreeFiveRetainedBlockKernel block P N = Vbar := by
    simpa only [Vbar] using
      degreeFourZeroCore_retainedBlockKernel_eq_translationImage
        block P hr hD N
  have hmapV : L.map (QuotientGroup.mk' N.1) = Vbar :=
    hmap.trans hretained
  let topEquiv : (Q ⧸ Vbar) ≃* (G ⧸ L) :=
    (QuotientGroup.quotientMulEquivOfEq hmapV.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient
        N.1 L le_sup_right)
  have hsectionC : PrimeSectionalRankBound C.p (Q ⧸ Vbar)
      (Nat.card block.Points / C.p) :=
    PrimeSectionalRankBound.of_injective C.p
      (degreeFiveRetainedTop_primeSectionalRank block P C.p N)
      topEquiv.toMonoidHom topEquiv.injective
  have hsection : PrimeSectionalRankBound C.p (Q ⧸ Vbar)
      (Nat.card block.Points / 2) := by
    simpa only [hC2] using hsectionC
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V ↦ C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  letI : Finite C.quotientRepresentation := inferInstanceAs (Finite C.V)
  letI : Finite (sigma.asModule ⧸ T.toSubmodule) :=
    Finite.of_surjective T.toSubmodule.mkQ T.toSubmodule.mkQ_surjective
  have hrank : Module.finrank (ZMod C.p)
      (PrimeCharacters C.p
        (Multiplicative (sigma.asModule ⧸ T.toSubmodule))) ≤
      Nat.card block.Points / 2 :=
    primeCharacterRank_le_of_injective C.p hsection embedding hembedding
  have hfinrank : Module.finrank (ZMod C.p)
      (sigma.asModule ⧸ T.toSubmodule) ≤ Nat.card block.Points / 2 := by
    rw [← primeCharacterRank_multiplicative C.p
      (sigma.asModule ⧸ T.toSubmodule)]
    exact hrank
  simpa only [Nat.mul_comm] using
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hfinrank

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
