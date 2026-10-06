import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFiniteFrameSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourCoarseNonzeroMenu
import SymmetricSubgroupAsymptotics.NonPrimeAbelianSoclePart
import SymmetricSubgroupAsymptotics.NonabelianSoclePartCenterless

/-!
# Nonbinary socle types in the degree-four zero core

When the ternary linear core vanishes, the whole retained block kernel is
the image of the elementary binary translation intersection.  Every odd
abelian socle type is disjoint from this image by coprime order, and every
nonabelian socle type is disjoint from it by centerlessness.  Both families
therefore embed in a section of the literal block top and inherit the
published McIver--Neumann half-degree generator bound.
-/

set_option autoImplicit false
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

/-- The actual degree-four translation intersection is a binary group. -/
theorem degreeFour_translationIntersection_isPGroup
    (hr : Nat.card block.Fibre = 4) :
    IsPGroup 2 (E block P) := by
  let C := elementaryChart block P
  letI : Fact C.p.Prime := C.primeFact
  letI : Finite C.V := Module.finite_of_finite (ZMod C.p)
  have hcard : Nat.card (E block P) = C.p ^
      Module.finrank (ZMod C.p) C.V := by
    calc
      Nat.card (E block P) = Nat.card (Multiplicative C.V) :=
        Nat.card_congr C.equiv.toEquiv
      _ = Nat.card C.V := rfl
      _ = C.p ^ Module.finrank (ZMod C.p) C.V := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod C.p), Nat.card_zmod]
  have hp : C.p = 2 := by
    change P.p = 2
    exact (degreeFour_translationDimension block P hr).1
  apply IsPGroup.of_card
  simpa only [hp] using hcard

/-- The elementary translation intersection is commutative in its literal
prime-field chart. -/
theorem degreeFour_translationIntersection_commutative :
    IsMulCommutative (E block P) := by
  let C := elementaryChart block P
  exact IsMulCommutative.of_comm fun x y ↦ by
    apply C.equiv.injective
    simpa only [map_mul] using
      (mul_comm (C.equiv x) (C.equiv y))

/-- The retained translation image remains a binary group. -/
theorem degreeFourTranslationImage_isPGroup
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    IsPGroup 2 (degreeFourTranslationImage block P N) :=
  (degreeFour_translationIntersection_isPGroup block P hr).map
    (QuotientGroup.mk' N.1)

/-- The retained translation image remains commutative. -/
theorem degreeFourTranslationImage_commutative
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    IsMulCommutative (degreeFourTranslationImage block P N) := by
  letI : IsMulCommutative (E block P) :=
    degreeFour_translationIntersection_commutative block P
  exact IsMulCommutative.of_comm fun x y ↦ by
    let q := QuotientGroup.mk' N.1
    let f : E block P →* degreeFourTranslationImage block P N :=
      q.subgroupMap (E block P)
    obtain ⟨x₀, rfl⟩ :=
      MonoidHom.subgroupMap_surjective q (E block P) x
    obtain ⟨y₀, rfl⟩ :=
      MonoidHom.subgroupMap_surjective q (E block P) y
    exact (show Commute x₀ y₀ from mul_comm' x₀ y₀).map f

/-- In the zero-core branch the entire retained block kernel is exactly
the retained elementary translation image. -/
theorem degreeFourZeroCore_retainedBlockKernel_eq_translationImage
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    degreeFiveRetainedBlockKernel block P N =
      degreeFourTranslationImage block P N := by
  have hK : binaryAffineLinearBlockKernel block P = ⊥ :=
    degreeFourLinearBlockKernel_eq_bot_of_core_eq_bot block P hr hD
  change (((binaryAffineLinearBlockKernel block P).comap
      (QuotientGroup.mk' (E block P))).map
        (QuotientGroup.mk' N.1)) =
      (E block P).map (QuotientGroup.mk' N.1)
  rw [hK, MonoidHom.comap_bot, QuotientGroup.ker_mk']

/-- The nonbinary nonabelian socle sum. -/
abbrev degreeFourNonbinaryNonabelianSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  minimalNormalSoclePart (DegreeFourRetainedQuotient N)
    (fun M ↦ ¬ IsPGroup 2 M ∧ ¬ IsMulCommutative M)

/-- The nonbinary abelian socle sum. -/
abbrev degreeFourNonbinaryAbelianSoclePart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  minimalNormalSoclePart (DegreeFourRetainedQuotient N)
    (fun M ↦ ¬ IsPGroup 2 M ∧ IsMulCommutative M)

/-- All nonbinary socle types are the join of their nonabelian and abelian
parts. -/
theorem degreeFourNonbinarySoclePart_eq_sup_commutativityTypes
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    minimalNormalSoclePart (DegreeFourRetainedQuotient N)
        (fun M ↦ ¬ IsPGroup 2 M) =
      degreeFourNonbinaryNonabelianSoclePart N ⊔
        degreeFourNonbinaryAbelianSoclePart N := by
  apply le_antisymm
  · apply minimalNormalSoclePart_le_of
    intro M hM hMnon2
    by_cases hcomm : IsMulCommutative M
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K ↦ ¬ IsPGroup 2 K ∧ IsMulCommutative K)
          M hM ⟨hMnon2, hcomm⟩).trans le_sup_right
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K ↦ ¬ IsPGroup 2 K ∧ ¬ IsMulCommutative K)
          M hM ⟨hMnon2, hcomm⟩).trans le_sup_left
  · apply sup_le
    · apply minimalNormalSoclePart_le_of
      intro M hM htype
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K ↦ ¬ IsPGroup 2 K) M hM htype.1
    · apply minimalNormalSoclePart_le_of
      intro M hM htype
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K ↦ ¬ IsPGroup 2 K) M hM htype.1

/-- Every nonbinary socle type is carried simultaneously by the literal
block-top section in the zero-core branch. -/
theorem degreeFourZeroCore_nonbinary_normalGen_le_slots
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : 2 ≤ Nat.card block.Points)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen
        (minimalNormalSoclePart (DegreeFourRetainedQuotient N)
          (fun M ↦ ¬ IsPGroup 2 M)) ≤
      degreeFourSocleSlots (Nat.card block.Points) := by
  rw [degreeFourNonbinarySoclePart_eq_sup_commutativityTypes N]
  refine (normalGen_sup_le_max_of_noCommonNormalQuotient
    (degreeFourNonbinaryNonabelianSoclePart N)
    (degreeFourNonbinaryAbelianSoclePart N) ?_).trans ?_
  · exact noCommonNormalQuotient_nonabelian_commutativeSocleParts
      (DegreeFourRetainedQuotient N) (fun M ↦ ¬ IsPGroup 2 M)
  · apply max_le
    · apply degreeFourRetainedSelectedSoclePart_normalGen_le_slots
        block P hMN hs N
          (fun M ↦ ¬ IsPGroup 2 M ∧ ¬ IsMulCommutative M)
      rw [degreeFourZeroCore_retainedBlockKernel_eq_translationImage
        block P hr hD N]
      letI : IsMulCommutative (degreeFourTranslationImage block P N) :=
        degreeFourTranslationImage_commutative block P N
      exact nonabelianMinimalNormalSoclePart_inf_commutativeNormal_eq_bot
        (G := DegreeFourRetainedQuotient N)
        (fun M ↦ ¬ IsPGroup 2 M)
        (degreeFourTranslationImage block P N)
        (inferInstance : IsMulCommutative
          (degreeFourTranslationImage block P N))
    · apply degreeFourRetainedSelectedSoclePart_normalGen_le_slots
        block P hMN hs N
          (fun M ↦ ¬ IsPGroup 2 M ∧ IsMulCommutative M)
      rw [degreeFourZeroCore_retainedBlockKernel_eq_translationImage
        block P hr hD N]
      exact abelianNonPrimarySoclePart_inf_isPGroup_eq_bot 2
        (degreeFourTranslationImage block P N)
        (degreeFourTranslationImage_isPGroup block P hr N)

/-- Concrete eight-block row: the nonbinary types use at most four of the
five available positions. -/
theorem degreeFourZeroCore_nonbinary_normalGen_le_five
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen
        (minimalNormalSoclePart (DegreeFourRetainedQuotient N)
          (fun M ↦ ¬ IsPGroup 2 M)) ≤ 5 := by
  refine (degreeFourZeroCore_nonbinary_normalGen_le_slots
    block P hMN hr hD (by omega) N).trans ?_
  rw [hs]
  norm_num [degreeFourSocleSlots]

/-- Concrete sixteen-block row: the nonbinary types use at most eight of
the ten available positions. -/
theorem degreeFourZeroCore_nonbinary_normalGen_le_ten
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 16)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    MarkedC4.normalGen
        (minimalNormalSoclePart (DegreeFourRetainedQuotient N)
          (fun M ↦ ¬ IsPGroup 2 M)) ≤ 10 := by
  refine (degreeFourZeroCore_nonbinary_normalGen_le_slots
    block P hMN hr hD (by omega) N).trans ?_
  rw [hs]
  norm_num [degreeFourSocleSlots]

/-- Assembly form used by the finite-frame bridge.  After the intrinsic
nonbinary argument above, the only remaining input is the noncentral
binary-primary row.  In particular this constructor prevents the odd and
nonabelian socle types from being repeated in the final finite proof. -/
noncomputable def degreeFourZeroCoreNoncentralSocleBounds_of_binary
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : 2 ≤ Nat.card block.Points)
    {slots : ℕ}
    (hslots : degreeFourSocleSlots (Nat.card block.Points) ≤ slots)
    (hbinary :
      ∀ N : DegreeFourZeroCoreFiniteFrameNormalAxis
          (preE7NonPairAction w U),
        ¬ E block P ≤ N.1 →
        MarkedC4.normalGen
          (noncentralPrimeSoclePart 2
            (preE7NonPairAction w U ⧸ N.1)) ≤ slots) :
    DegreeFourZeroCoreNoncentralSocleBounds block P slots where
  noncentralBinary := hbinary
  nonbinary := by
    intro N _hretained
    exact (degreeFourZeroCore_nonbinary_normalGen_le_slots
      block P hMN hr hD hs N).trans hslots

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
