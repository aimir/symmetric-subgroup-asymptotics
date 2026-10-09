import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionTopLowerBound
import SymmetricSubgroupAsymptotics.TernaryPlaneKleinNormalizer

/-!
# The linear image of a proper two-sign section

Every proper section has a two-dimensional ternary kernel.  Its acting top
therefore has a canonical matrix image in `GL₂(3)`.  The surviving literal
pair kernel maps injectively to a normal elementary abelian subgroup of
order four in that image.  The ternary-plane Klein-normalizer theorem gives
the upper bound eight, while a sign-class exchanger gives the matching
lower bound.  Thus the matrix image has order exactly eight and the kernel
of the section action has order at most four.
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

/-- The signed quotient maps onto the actual acting top of every proper
section. -/
theorem degreeThreeFourBlockTwoSignSectionSignedTopHom_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P)) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignSectionSignedTopHom
        block P hr hs hcomponent N) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let D := (QuotientGroup.mk' (E block P)).ker ⊔
    degreeThreeFourBlockTwoSignSectionAxis block P N
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
  refine ⟨C.sourceEquiv (QuotientGroup.mk' (E block P) g), ?_⟩
  rw [degreeThreeFourBlockTwoSignSectionSignedTopHom_apply,
    C.sourceEquiv.symm_apply_apply]
  exact (elementaryChart block P).originalKernelChart.labelTop_apply
    (QuotientGroup.mk' (E block P))
    (degreeThreeFourBlockTwoSignSectionAxis block P N)
    (QuotientGroup.mk'_surjective (E block P)) g

/-- Matrix realization of the actual section action on its retained
two-dimensional ternary kernel.  This map need not be faithful; its kernel
is the residual binary layer handled by the central recursion. -/
noncomputable def degreeThreeFourBlockTwoSignSectionLinearMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N)) →*
      LinearThree.GL3 := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  let V := DegreeThreeFourBlockTwoSignSectionModule block P N
  have hfin : Module.finrank (ZMod P.p) V = 2 :=
    degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two
      block P hr hs hcomponent hbinary htwo N
  let basis : Module.Basis (Fin 2) (ZMod P.p) V :=
    Module.finBasisOfFinrankEq (ZMod P.p) V hfin
  let rho := (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ
  let phi0 : (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
      degreeThreeFourBlockTwoSignSectionAxis block P N)) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  let e : ZMod P.p ≃+* ZMod 3 := ZMod.ringEquivCongr hp
  exact (Matrix.GeneralLinearGroup.map e.toRingHom).comp phi0

/-- Equality in the chosen matrix realization reflects equality of the
underlying section operators. -/
theorem degreeThreeFourBlockTwoSignSectionLinearMap_reflects
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (x y : G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
      degreeThreeFourBlockTwoSignSectionAxis block P N))
    (hxy : degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N x =
      degreeThreeFourBlockTwoSignSectionLinearMap
        block P hr hs hcomponent hbinary htwo N y) :
    (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ x =
      (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ y := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  let V := DegreeThreeFourBlockTwoSignSectionModule block P N
  have hfin : Module.finrank (ZMod P.p) V = 2 :=
    degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two
      block P hr hs hcomponent hbinary htwo N
  let basis : Module.Basis (Fin 2) (ZMod P.p) V :=
    Module.finBasisOfFinrankEq (ZMod P.p) V hfin
  let rho := (degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ
  let phi0 : (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
      degreeThreeFourBlockTwoSignSectionAxis block P N)) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  let e : ZMod P.p ≃+* ZMod 3 := ZMod.ringEquivCongr hp
  have hphi0 : phi0 x = phi0 y := by
    apply Units.ext
    ext i j
    apply e.injective
    have hij := congrArg (fun g : LinearThree.GL3 => g i j) hxy
    simpa only [degreeThreeFourBlockTwoSignSectionLinearMap, phi0, e,
      MonoidHom.comp_apply] using hij
  have hrho : Representation.asGroupHom rho x =
      Representation.asGroupHom rho y := by
    apply (Matrix.GeneralLinearGroup.toLin' basis).symm.injective
    simpa only [phi0, MonoidHom.comp_apply] using hphi0
  exact congrArg Units.val hrho

/-- Restriction of the section matrix action to the surviving literal pair
kernel. -/
def degreeThreeFourBlockTwoSignSectionPairLinearMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker →* LinearThree.GL3 :=
  (degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N).comp
      (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N)

theorem degreeThreeFourBlockTwoSignSectionPairLinearMap_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Injective
      (degreeThreeFourBlockTwoSignSectionPairLinearMap
        block P hr hs hcomponent hbinary htwo N) := by
  intro x y hxy
  apply degreeThreeFourBlockTwoSignSectionPairKernelRepresentation_injective
    block P hr hs hcomponent hbinary htwo N
  exact degreeThreeFourBlockTwoSignSectionLinearMap_reflects
    block P hr hs hcomponent hbinary htwo N _ _ hxy

/-- The matrix pair-kernel image is a literal Klein four group. -/
theorem degreeThreeFourBlockTwoSignSectionPairLinearRange_card
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (degreeThreeFourBlockTwoSignSectionPairLinearMap
      block P hr hs hcomponent hbinary htwo N).range = 4 := by
  let f := degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N
  calc
    Nat.card f.range = Nat.card
        (degreeThreeFourBlockPairChart
          block P hr hs hcomponent).frame.top.ker :=
      Nat.card_congr
        (MonoidHom.ofInjective
          (degreeThreeFourBlockTwoSignSectionPairLinearMap_injective
            block P hr hs hcomponent hbinary htwo N)).toEquiv.symm
    _ = 4 := degreeThreeFourBlockTwoSign_pairKernel_card
      block P hr hs hcomponent htwo

/-- Every element of the matrix pair-kernel image has square one. -/
theorem degreeThreeFourBlockTwoSignSectionPairLinearRange_square
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (z : (degreeThreeFourBlockTwoSignSectionPairLinearMap
      block P hr hs hcomponent hbinary htwo N).range) :
    z ^ 2 = 1 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let f := degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N
  obtain ⟨k, rfl⟩ := z.2
  apply Subtype.ext
  rw [← map_pow]
  have hk : k ^ 2 = 1 := by
    apply C.frame.bitsHom_injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.toAdd.injective
    change C.frame.bits k + C.frame.bits k = 0
    funext i
    exact CharTwo.add_self_eq_zero _
  rw [hk, map_one]

private theorem degreeThreeFourBlockTwoSignSectionPairTopRange_normal
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (N : TwoSignProperAxis (E block P)) :
    (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
      block P hr hs hcomponent N).range.Normal := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let f := degreeThreeFourBlockTwoSignSectionSignedTopHom
    block P hr hs hcomponent N
  let K := C.frame.top.ker
  have hf : Function.Surjective f :=
    degreeThreeFourBlockTwoSignSectionSignedTopHom_surjective
      block P hr hs hcomponent N
  have hnormal : (K.map f).Normal :=
    Subgroup.Normal.map (show K.Normal from inferInstance) f hf
  have heq : K.map f =
      (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N).range := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k.1, k.2, rfl⟩
  rw [← heq]
  exact hnormal

/-- The matrix pair-kernel image is normal in the full section matrix
image. -/
theorem degreeThreeFourBlockTwoSignSectionPairLinearRange_normal
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    let phi := degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N
    let psi := degreeThreeFourBlockTwoSignSectionPairLinearMap
      block P hr hs hcomponent hbinary htwo N
    (psi.range.subgroupOf phi.range).Normal := by
  let phi := degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N
  let psi := degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N
  let L := (degreeThreeFourBlockTwoSignSectionPairKernelTopHom
    block P hr hs hcomponent N).range
  have hL : L.Normal :=
    degreeThreeFourBlockTwoSignSectionPairTopRange_normal
      block P hr hs hcomponent N
  have hle : psi.range ≤ phi.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSignSectionPairKernelTopHom
      block P hr hs hcomponent N k, rfl⟩
  apply (Subgroup.normal_subgroupOf_iff hle).mpr
  intro k h hk hh
  obtain ⟨x, hx⟩ := hk
  obtain ⟨t, ht⟩ := hh
  have hxL : degreeThreeFourBlockTwoSignSectionPairKernelTopHom
      block P hr hs hcomponent N x ∈ L := ⟨x, rfl⟩
  have hconj := hL.conj_mem _ hxL t
  obtain ⟨y, hy⟩ := hconj
  refine ⟨y, ?_⟩
  rw [← hx, ← ht, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg phi hy

/-- The full matrix image of a proper two-sign section has order at most
eight. -/
theorem degreeThreeFourBlockTwoSignSectionLinearRange_card_le_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N).range ≤ 8 := by
  let phi := degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N
  let psi := degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N
  have hle : psi.range ≤ phi.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSignSectionPairKernelTopHom
      block P hr hs hcomponent N k, rfl⟩
  exact LinearThree.card_le_eight_of_normalizes_klein
    phi.range psi.range hle
    (degreeThreeFourBlockTwoSignSectionPairLinearRange_normal
      block P hr hs hcomponent hbinary htwo N)
    (degreeThreeFourBlockTwoSignSectionPairLinearRange_card
      block P hr hs hcomponent hbinary htwo N)
    (degreeThreeFourBlockTwoSignSectionPairLinearRange_square
      block P hr hs hcomponent hbinary htwo N)

/-- A sign-class exchanger has matrix image outside the Klein pair-kernel
image. -/
theorem degreeThreeFourBlockTwoSignSection_exists_linear_outside_pairRange
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
      degreeThreeFourBlockTwoSignSectionLinearMap
          block P hr hs hcomponent hbinary htwo N
          (degreeThreeFourBlockTwoSignSectionSignedTopHom
            block P hr hs hcomponent N u) ∉
        (degreeThreeFourBlockTwoSignSectionPairLinearMap
          block P hr hs hcomponent hbinary htwo N).range := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let F := C.frame
  let phi := degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N
  let f := degreeThreeFourBlockTwoSignSectionSignedTopHom
    block P hr hs hcomponent N
  let psi := degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N
  obtain ⟨u, k₀, hconj⟩ :=
    degreeThreeFourBlockTwoSign_exists_pairKernel_conjugate_ne
      block P hr hs hcomponent htwo
  refine ⟨u, ?_⟩
  rintro ⟨k, hk⟩
  have hcomm : k * k₀ = k₀ * k := by
    apply F.bitsHom_injective
    rw [map_mul, map_mul, mul_comm]
  have hconjMap : psi (MulAut.conjNormal u k₀) = psi k₀ := by
    change phi (f (u * (k₀ : C.action) * u⁻¹)) = phi (f k₀)
    rw [map_mul, map_mul, map_inv, hk,
      ← degreeThreeFourBlockTwoSignSectionSignedTopHom_pairKernel,
      ← degreeThreeFourBlockTwoSignSectionSignedTopHom_pairKernel,
      ← map_mul, hcomm, map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  exact hconj
    (degreeThreeFourBlockTwoSignSectionPairLinearMap_injective
      block P hr hs hcomponent hbinary htwo N hconjMap)

/-- The section matrix image is exactly an order-eight binary subgroup of
`GL₂(3)`. -/
theorem degreeThreeFourBlockTwoSignSectionLinearRange_card_eq_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N).range = 8 := by
  let phi := degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N
  let psi := degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N
  let K := psi.range.subgroupOf phi.range
  have hKcard : Nat.card K = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
      rintro _ ⟨k, rfl⟩
      exact ⟨degreeThreeFourBlockTwoSignSectionPairKernelTopHom
        block P hr hs hcomponent N k, rfl⟩)).toEquiv]
    exact degreeThreeFourBlockTwoSignSectionPairLinearRange_card
      block P hr hs hcomponent hbinary htwo N
  obtain ⟨u, hu⟩ :=
    degreeThreeFourBlockTwoSignSection_exists_linear_outside_pairRange
      block P hr hs hcomponent hbinary htwo N
  have hKne : K ≠ ⊤ := by
    intro htop
    apply hu
    change phi (degreeThreeFourBlockTwoSignSectionSignedTopHom
      block P hr hs hcomponent N u) ∈ psi.range
    have hmem : (⟨phi (degreeThreeFourBlockTwoSignSectionSignedTopHom
      block P hr hs hcomponent N u), ⟨_, rfl⟩⟩ : phi.range) ∈ K := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  have hindex : 1 < K.index := Subgroup.one_lt_index_of_ne_top hKne
  have hcard := K.card_mul_index
  have hupper := degreeThreeFourBlockTwoSignSectionLinearRange_card_le_eight
    block P hr hs hcomponent hbinary htwo N
  rw [hKcard] at hcard
  omega

/-- The kernel left above the dihedral matrix image has order at most four. -/
theorem degreeThreeFourBlockTwoSignSectionLinearMap_kernel_card_le_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Nat.card (degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N).ker ≤ 4 := by
  let phi := degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N
  have htop := degreeThreeFourBlockTwoSignSectionTop_card_le_thirty_two
    block P hr hs hcomponent hbinary htwo N
  have himage :=
    degreeThreeFourBlockTwoSignSectionLinearRange_card_eq_eight
      block P hr hs hcomponent hbinary htwo N
  have hcard := phi.ker.card_mul_index
  rw [Subgroup.index_ker, himage] at hcard
  omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
