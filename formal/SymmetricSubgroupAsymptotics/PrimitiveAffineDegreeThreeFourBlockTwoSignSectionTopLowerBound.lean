import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionPairKernelFaithful

/-!
# The proper two-sign section top contains a dihedral-sized subgroup

The faithful literal pair kernel contributes a copy of `C₂²`.  Transitivity
of the original four-coordinate top supplies an element exchanging the two
sign classes.  Its image in the section top cannot lie in that binary
square: otherwise conjugation would fix the whole pair kernel, contrary to
the exchanged literal bit characters.  Hence every proper section top has
order at least eight.
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

private abbrev G := preE7NonPairAction w U

/-- The whole literal signed quotient maps to the acting top of every proper
section. -/
def degreeThreeFourBlockTwoSignSectionSignedTopHom
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P)) :
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action →*
      G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let pi := QuotientGroup.mk' (E block P)
  let M := degreeThreeFourBlockTwoSignSectionAxis block P N
  exact (OriginalKernelModuleChart.sectionLabelTop
    pi M (QuotientGroup.mk'_surjective (E block P))).comp
      C.sourceEquiv.symm.toMonoidHom

@[simp] theorem degreeThreeFourBlockTwoSignSectionSignedTopHom_apply
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P))
    (u : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).action) :
    degreeThreeFourBlockTwoSignSectionSignedTopHom
        block P hr hs hcomponent N u =
      OriginalKernelModuleChart.sectionLabelTop
        (QuotientGroup.mk' (E block P))
        (degreeThreeFourBlockTwoSignSectionAxis block P N)
        (QuotientGroup.mk'_surjective (E block P))
        ((degreeThreeFourBlockPairChart
          block P hr hs hcomponent).sourceEquiv.symm u) := rfl

@[simp] theorem degreeThreeFourBlockTwoSignSectionSignedTopHom_pairKernel
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P))
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker) :
    degreeThreeFourBlockTwoSignSectionSignedTopHom
        block P hr hs hcomponent N k.1 =
      degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N k := rfl

/-- The transitive four-coordinate top conjugates some literal pair-kernel
element nontrivially.  This statement is independent of the later section
and can therefore be reused after applying any representation which stays
faithful on the pair kernel. -/
theorem degreeThreeFourBlockTwoSign_exists_pairKernel_conjugate_ne
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2) :
    ∃ (u : (degreeThreeFourBlockPairChart
          block P hr hs hcomponent).action)
      (k : (degreeThreeFourBlockPairChart
          block P hr hs hcomponent).frame.top.ker),
      MulAut.conjNormal u k ≠ k := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let F := C.frame
  have htwo' : Nat.card (BinaryPairFrame.FourCoordinateSign F) = 2 := by
    simpa only [degreeThreeFourBlockSignedIsotypeProfile,
      BinaryPairFrame.fourCoordinateSignedIsotypeProfile,
      DegreeThreeFourBlockSignedIsotypeProfile.isotypeCount, C, F] using htwo
  let i₀ := BinaryPairFrame.twoSignCoordinate F htwo' 0
  let i₁ := BinaryPairFrame.twoSignCoordinate F htwo' 1
  let target : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd 1, 1)
  obtain ⟨k₀, hk₀⟩ :=
    BinaryPairFrame.twoSignKernelHom_surjective F C.pretransitive htwo' target
  letI : MulAction.IsPretransitive C.action (Fin (2 * 4)) := C.pretransitive
  letI : MulAction.IsPretransitive F.top.range (Fin 4) := F.top_pretransitive
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq F.top.range i₀ i₁
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective t
  have htop : F.top u i₀ = i₁ := by
    change (F.top.rangeRestrict u : Equiv.Perm (Fin 4)) i₀ = i₁
    rw [hu]
    exact ht
  have hkbit₀ : F.bits k₀ i₀ = 1 := by
    have h := congrArg Prod.fst hk₀
    change Multiplicative.ofAdd (F.bits k₀ i₀) =
      Multiplicative.ofAdd 1 at h
    exact congrArg Multiplicative.toAdd h
  have hkbit₁ : F.bits k₀ i₁ = 0 := by
    have h := congrArg Prod.snd hk₀
    change Multiplicative.ofAdd (F.bits k₀ i₁) = 1 at h
    exact congrArg Multiplicative.toAdd h
  have hconj : MulAut.conjNormal u k₀ ≠ k₀ := by
    intro he
    have hbits := congrArg (fun k : F.top.ker => F.bits k i₁) he
    change F.bits (MulAut.conjNormal u k₀) i₁ = F.bits k₀ i₁ at hbits
    rw [F.bits_conjNormal] at hbits
    have hinv : (F.top u)⁻¹ i₁ = i₀ := by
      rw [← htop]
      exact (F.top u).symm_apply_apply i₀
    rw [hinv, hkbit₀, hkbit₁] at hbits
    exact one_ne_zero hbits
  exact ⟨u, k₀, hconj⟩

/-- A sign-class exchanger survives outside the image of the literal pair
kernel in every proper section top. -/
theorem degreeThreeFourBlockTwoSignSection_exists_top_outside_pairKernel
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    ∃ u : (degreeThreeFourBlockPairChart
        block P hr hs hcomponent).action,
      degreeThreeFourBlockTwoSignSectionSignedTopHom
          block P hr hs hcomponent N u ∉
        (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
          block P hr hs hcomponent N).range := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let F := C.frame
  obtain ⟨u, k₀, hconj⟩ :=
    degreeThreeFourBlockTwoSign_exists_pairKernel_conjugate_ne
      block P hr hs hcomponent htwo
  refine ⟨u, ?_⟩
  rintro ⟨k, hk⟩
  have hcomm : k * k₀ = k₀ * k := by
    apply F.bitsHom_injective
    rw [map_mul, map_mul, mul_comm]
  have hcomm' :
      (k : C.action) * (k₀ : C.action) =
        (k₀ : C.action) * (k : C.action) := by
    have := congrArg (fun z : F.top.ker => (z : C.action)) hcomm
    simpa using this
  have hconjMap :
      degreeThreeFourBlockTwoSignSectionPairKernelTopHom
          block P hr hs hcomponent N (MulAut.conjNormal u k₀) =
        degreeThreeFourBlockTwoSignSectionPairKernelTopHom
          block P hr hs hcomponent N k₀ := by
    let f := degreeThreeFourBlockTwoSignSectionSignedTopHom
      block P hr hs hcomponent N
    rw [← degreeThreeFourBlockTwoSignSectionSignedTopHom_pairKernel,
      ← degreeThreeFourBlockTwoSignSectionSignedTopHom_pairKernel]
    change f (MulAut.conjNormal u k₀ : C.action) = f (k₀ : C.action)
    change f (u * (k₀ : C.action) * u⁻¹) = f (k₀ : C.action)
    rw [map_mul, map_mul, map_inv]
    have hku : f (k : C.action) = f u := by
      rw [degreeThreeFourBlockTwoSignSectionSignedTopHom_pairKernel]
      exact hk
    rw [← hku, ← map_mul, hcomm', map_mul]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  exact hconj
    (degreeThreeFourBlockTwoSignSectionPairKernelTopHom_injective
      block P hr hs hcomponent hbinary htwo N hconjMap)

/-- Every proper literal two-sign section top has order at least eight. -/
theorem degreeThreeFourBlockTwoSignSectionTop_card_ge_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    8 ≤ Nat.card
      (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N)) := by
  let f := degreeThreeFourBlockTwoSignSectionPairKernelTopHom
    block P hr hs hcomponent N
  let K := f.range
  have hf : Function.Injective f :=
    degreeThreeFourBlockTwoSignSectionPairKernelTopHom_injective
      block P hr hs hcomponent hbinary htwo N
  have hK : Nat.card K = 4 := by
    calc
      Nat.card K = Nat.card
          (degreeThreeFourBlockPairChart
            block P hr hs hcomponent).frame.top.ker :=
        Nat.card_congr
          (MulEquiv.ofBijective f.rangeRestrict
            ⟨fun x y h ↦ hf (congrArg Subtype.val h),
              f.rangeRestrict_surjective⟩).symm.toEquiv
      _ = 4 := degreeThreeFourBlockTwoSign_pairKernel_card
        block P hr hs hcomponent htwo
  obtain ⟨u, hu⟩ :=
    degreeThreeFourBlockTwoSignSection_exists_top_outside_pairKernel
      block P hr hs hcomponent hbinary htwo N
  have hKne : K ≠ ⊤ := by
    intro htop
    apply hu
    change degreeThreeFourBlockTwoSignSectionSignedTopHom
      block P hr hs hcomponent N u ∈ K
    rw [htop]
    exact Subgroup.mem_top _
  have hindex : 1 < K.index := Subgroup.one_lt_index_of_ne_top hKne
  calc
    8 = 4 * 2 := by norm_num
    _ ≤ 4 * K.index := Nat.mul_le_mul_left 4 (by omega)
    _ = Nat.card K * K.index := by rw [hK]
    _ = Nat.card
        (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
          degreeThreeFourBlockTwoSignSectionAxis block P N)) :=
      K.card_mul_index

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
