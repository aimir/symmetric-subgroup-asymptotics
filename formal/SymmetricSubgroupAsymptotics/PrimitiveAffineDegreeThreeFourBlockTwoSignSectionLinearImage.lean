import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionTopLowerBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionOrder
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
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Matrix

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
  exact OriginalKernelModuleChart.sectionLabelTop_apply
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

/-- Additive coordinates on the retained section, using the same chosen
basis and scalar transport as its matrix realization. -/
noncomputable def degreeThreeFourBlockTwoSignSectionCoordinateEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    DegreeThreeFourBlockTwoSignSectionModule block P N ≃+
      DegreeSixS3Wreath.TernaryPlane := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  let V := DegreeThreeFourBlockTwoSignSectionModule block P N
  have hfin : Module.finrank (ZMod P.p) V = 2 :=
    degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two
      block P hr hs hcomponent hbinary htwo N
  let basis : Module.Basis (Fin 2) (ZMod P.p) V :=
    Module.finBasisOfFinrankEq (ZMod P.p) V hfin
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  let e : ZMod P.p ≃+* ZMod 3 := ZMod.ringEquivCongr hp
  exact basis.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ : Fin 2 => e.toAddEquiv)

/-- The chosen section coordinates turn its literal representation into
the action of the matrix exported above. -/
theorem degreeThreeFourBlockTwoSignSectionCoordinateEquiv_action
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (x : G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
      degreeThreeFourBlockTwoSignSectionAxis block P N))
    (v : DegreeThreeFourBlockTwoSignSectionModule block P N) :
    degreeThreeFourBlockTwoSignSectionCoordinateEquiv
        block P hr hs hcomponent hbinary htwo N
        ((degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ x v) =
      (Matrix.GeneralLinearGroup.toLin'
        (Pi.basisFun (ZMod 3) (Fin 2))
          (degreeThreeFourBlockTwoSignSectionLinearMap
            block P hr hs hcomponent hbinary htwo N x)).toLinearEquiv
        (degreeThreeFourBlockTwoSignSectionCoordinateEquiv
          block P hr hs hcomponent hbinary htwo N v) := by
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
  have hoperator :
      Matrix.GeneralLinearGroup.toLin' basis (phi0 x) =
        Representation.asGroupHom rho x := by
    dsimp only [phi0, MonoidHom.comp_apply]
    change Matrix.GeneralLinearGroup.toLin' basis
        ((Matrix.GeneralLinearGroup.toLin' basis).symm
          (Representation.asGroupHom rho x)) =
      Representation.asGroupHom rho x
    exact (Matrix.GeneralLinearGroup.toLin' basis).apply_symm_apply _
  have hcoords : basis.equivFun (rho x v) =
      (phi0 x : Matrix (Fin 2) (Fin 2) (ZMod P.p)) *ᵥ
        basis.equivFun v := by
    have happ := congrArg
      (fun L : LinearMap.GeneralLinearGroup (ZMod P.p) V =>
        (L : Module.End (ZMod P.p) V) v) hoperator
    have hcomb (z : Fin 2 → ZMod P.p) :
        basis.equivFun (Fintype.linearCombination (ZMod P.p) basis z) = z := by
      rw [Fintype.linearCombination_apply,
        ← Module.Basis.equivFun_symm_apply]
      exact basis.equivFun.apply_symm_apply z
    calc
      basis.equivFun (rho x v) =
          basis.equivFun
            ((Matrix.GeneralLinearGroup.toLin' basis (phi0 x)).toLinearEquiv v) :=
        congrArg basis.equivFun happ.symm
      _ = (phi0 x : Matrix (Fin 2) (Fin 2) (ZMod P.p)) *ᵥ
          basis.equivFun v := by
        rw [Matrix.GeneralLinearGroup.toLin'_apply, hcomb]
        rfl
  funext i
  change e (basis.equivFun (rho x v) i) =
    (((phi0 x : Matrix (Fin 2) (Fin 2) (ZMod P.p)).map e.toRingHom) *ᵥ
      (fun j => e (basis.equivFun v j))) i
  rw [hcoords]
  exact RingHom.map_mulVec e.toRingHom
    (phi0 x : Matrix (Fin 2) (Fin 2) (ZMod P.p)) (basis.equivFun v) i

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

/-- The same faithful pair-kernel image with the source relabelled as the
standard `C₂²`. -/
def degreeThreeFourBlockTwoSignSectionPairBitsLinearMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →*
      LinearThree.GL3 :=
  (degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N).comp
      (degreeThreeFourBlockTwoSign_pairKernelEquiv
        block P hr hs hcomponent htwo).symm.toMonoidHom

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

theorem degreeThreeFourBlockTwoSignSectionPairBitsLinearMap_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Injective
      (degreeThreeFourBlockTwoSignSectionPairBitsLinearMap
        block P hr hs hcomponent hbinary htwo N) :=
  (degreeThreeFourBlockTwoSignSectionPairLinearMap_injective
    block P hr hs hcomponent hbinary htwo N).comp
      (degreeThreeFourBlockTwoSign_pairKernelEquiv
        block P hr hs hcomponent htwo).symm.injective

theorem degreeThreeFourBlockTwoSignSectionPairBitsLinearMap_range
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    (degreeThreeFourBlockTwoSignSectionPairBitsLinearMap
      block P hr hs hcomponent hbinary htwo N).range =
      (degreeThreeFourBlockTwoSignSectionPairLinearMap
        block P hr hs hcomponent hbinary htwo N).range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨(degreeThreeFourBlockTwoSign_pairKernelEquiv
      block P hr hs hcomponent htwo).symm x, rfl⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSign_pairKernelEquiv
      block P hr hs hcomponent htwo k, by
        simp only [degreeThreeFourBlockTwoSignSectionPairBitsLinearMap,
          MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply]⟩

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
  obtain ⟨k, hk⟩ := z.2
  apply Subtype.ext
  change (z : LinearThree.GL3) ^ 2 = 1
  rw [← hk]
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
  rw [← hx, ← ht]
  simp only [psi, degreeThreeFourBlockTwoSignSectionPairLinearMap,
    MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
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
  let f := degreeThreeFourBlockTwoSignSectionPairBitsLinearMap
    block P hr hs hcomponent hbinary htwo N
  have hfrange : f.range = psi.range :=
    degreeThreeFourBlockTwoSignSectionPairBitsLinearMap_range
      block P hr hs hcomponent hbinary htwo N
  have hle : psi.range ≤ phi.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSignSectionPairKernelTopHom
      block P hr hs hcomponent N k, rfl⟩
  have hfle : f.range ≤ phi.range := hfrange.trans_le hle
  have hfnormal : (f.range.subgroupOf phi.range).Normal := by
    rw [hfrange]
    exact degreeThreeFourBlockTwoSignSectionPairLinearRange_normal
      block P hr hs hcomponent hbinary htwo N
  exact LinearThree.card_le_eight_of_normalizes_kleinRange
    phi.range f
      (degreeThreeFourBlockTwoSignSectionPairBitsLinearMap_injective
        block P hr hs hcomponent hbinary htwo N)
      hfle hfnormal

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
  have hcomm' :
      (k : C.action) * (k₀ : C.action) =
        (k₀ : C.action) * (k : C.action) := by
    have := congrArg (fun z : F.top.ker => (z : C.action)) hcomm
    simpa using this
  have hconjMap : psi (MulAut.conjNormal u k₀) = psi k₀ := by
    change phi (f (u * (k₀ : C.action) * u⁻¹)) =
      phi (f (k₀ : C.action))
    simp only [map_mul, map_inv]
    have hku : phi (f (k : C.action)) = phi (f u) := by
      change psi k = phi (f u)
      exact hk
    rw [← hku, ← map_mul phi, ← map_mul f,
      hcomm', map_mul f, map_mul phi]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
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
  change Nat.card phi.range ≤ 8 at hupper
  rw [hKcard] at hcard
  have hlower : 8 ≤ Nat.card phi.range := by
    calc
      8 = 4 * 2 := by norm_num
      _ ≤ 4 * K.index := Nat.mul_le_mul_left 4 (by omega)
      _ = Nat.card phi.range := hcard
  change Nat.card phi.range = 8
  omega

/-- The exact order-eight matrix image is carried to the standard
monomial `D8` action by one change of basis. -/
noncomputable def degreeThreeFourBlockTwoSignSectionLinearRangeD8Conjugacy
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    LinearThree.SubgroupD8Conjugacy
      (degreeThreeFourBlockTwoSignSectionLinearMap
        block P hr hs hcomponent hbinary htwo N).range := by
  let phi := degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N
  let psi := degreeThreeFourBlockTwoSignSectionPairLinearMap
    block P hr hs hcomponent hbinary htwo N
  let f := degreeThreeFourBlockTwoSignSectionPairBitsLinearMap
    block P hr hs hcomponent hbinary htwo N
  have hfrange : f.range = psi.range :=
    degreeThreeFourBlockTwoSignSectionPairBitsLinearMap_range
      block P hr hs hcomponent hbinary htwo N
  have hle : psi.range ≤ phi.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSignSectionPairKernelTopHom
      block P hr hs hcomponent N k, rfl⟩
  have hfle : f.range ≤ phi.range := hfrange.trans_le hle
  have hfnormal : (f.range.subgroupOf phi.range).Normal := by
    rw [hfrange]
    exact degreeThreeFourBlockTwoSignSectionPairLinearRange_normal
      block P hr hs hcomponent hbinary htwo N
  exact
    LinearThree.subgroupD8Conjugacy_of_card_eight_of_normalizes_kleinRange
      phi.range f
        (degreeThreeFourBlockTwoSignSectionPairBitsLinearMap_injective
          block P hr hs hcomponent hbinary htwo N)
        hfle hfnormal
        (degreeThreeFourBlockTwoSignSectionLinearRange_card_eq_eight
          block P hr hs hcomponent hbinary htwo N)

/-- The group equivalence underlying the action-compatible section
recognition. -/
noncomputable def degreeThreeFourBlockTwoSignSectionLinearRangeEquivD8
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    (degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N).range ≃*
        DegreeSixS3Wreath.D8 :=
  (degreeThreeFourBlockTwoSignSectionLinearRangeD8Conjugacy
    block P hr hs hcomponent hbinary htwo N).equiv

/-- The actual section top maps onto the standard dihedral group through
its faithful order-eight matrix image. -/
noncomputable def degreeThreeFourBlockTwoSignSectionD8Map
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
        DegreeSixS3Wreath.D8 :=
  (degreeThreeFourBlockTwoSignSectionLinearRangeEquivD8
      block P hr hs hcomponent hbinary htwo N).toMonoidHom.comp
    (degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N).rangeRestrict

theorem degreeThreeFourBlockTwoSignSectionD8Map_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignSectionD8Map
        block P hr hs hcomponent hbinary htwo N) :=
  (degreeThreeFourBlockTwoSignSectionLinearRangeEquivD8
      block P hr hs hcomponent hbinary htwo N).surjective.comp
    (degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N).rangeRestrict_surjective

/-- Matrix compatibility retained by the section's dihedral quotient.
This is the input needed to transport the full ternary semidirect product,
and is stronger than an abstract identification of the order-eight top. -/
theorem degreeThreeFourBlockTwoSignSectionD8Map_matrix
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (x : G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
      degreeThreeFourBlockTwoSignSectionAxis block P N)) :
    let D := degreeThreeFourBlockTwoSignSectionLinearRangeD8Conjugacy
      block P hr hs hcomponent hbinary htwo N
    DegreeSixS3Wreath.standardD8LinearMap
        (degreeThreeFourBlockTwoSignSectionD8Map
          block P hr hs hcomponent hbinary htwo N x) =
      D.conjugator *
        degreeThreeFourBlockTwoSignSectionLinearMap
          block P hr hs hcomponent hbinary htwo N x *
        D.conjugator⁻¹ := by
  let D := degreeThreeFourBlockTwoSignSectionLinearRangeD8Conjugacy
    block P hr hs hcomponent hbinary htwo N
  exact D.matrix_eq
    ((degreeThreeFourBlockTwoSignSectionLinearMap
      block P hr hs hcomponent hbinary htwo N).rangeRestrict x)

/-- Coordinates on the retained section after the change of basis which
puts its dihedral action into the fixed degree-six monomial form. -/
noncomputable def degreeThreeFourBlockTwoSignSectionTernaryEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P)) :
    DegreeThreeFourBlockTwoSignSectionModule block P N ≃+
      DegreeSixS3Wreath.TernaryPlane :=
  (degreeThreeFourBlockTwoSignSectionCoordinateEquiv
    block P hr hs hcomponent hbinary htwo N).trans
      (Matrix.GeneralLinearGroup.toLin'
        (Pi.basisFun (ZMod 3) (Fin 2))
          (degreeThreeFourBlockTwoSignSectionLinearRangeD8Conjugacy
            block P hr hs hcomponent hbinary htwo N).conjugator).toLinearEquiv.toAddEquiv

/-- The preceding coordinate equivalence intertwines the actual section
action with the standard `D8` action on `C₃²`. -/
theorem degreeThreeFourBlockTwoSignSectionTernaryEquiv_action
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (x : G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
      degreeThreeFourBlockTwoSignSectionAxis block P N))
    (v : DegreeThreeFourBlockTwoSignSectionModule block P N) :
    degreeThreeFourBlockTwoSignSectionTernaryEquiv
        block P hr hs hcomponent hbinary htwo N
        ((degreeThreeFourBlockTwoSignSectionRepresentation block P N).ρ x v) =
      DegreeSixS3Wreath.monomialRepresentation
        (degreeThreeFourBlockTwoSignSectionD8Map
          block P hr hs hcomponent hbinary htwo N x)
        (degreeThreeFourBlockTwoSignSectionTernaryEquiv
          block P hr hs hcomponent hbinary htwo N v) := by
  let c := degreeThreeFourBlockTwoSignSectionCoordinateEquiv
    block P hr hs hcomponent hbinary htwo N
  let D := degreeThreeFourBlockTwoSignSectionLinearRangeD8Conjugacy
    block P hr hs hcomponent hbinary htwo N
  let b := Pi.basisFun (ZMod 3) (Fin 2)
  let g := Matrix.GeneralLinearGroup.toLin' b D.conjugator
  let phi := degreeThreeFourBlockTwoSignSectionLinearMap
    block P hr hs hcomponent hbinary htwo N
  let d := degreeThreeFourBlockTwoSignSectionD8Map
    block P hr hs hcomponent hbinary htwo N
  have hc := degreeThreeFourBlockTwoSignSectionCoordinateEquiv_action
    block P hr hs hcomponent hbinary htwo N x v
  have hm := congrArg
    (fun A : LinearThree.GL3 =>
      (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv
        (g.toLinearEquiv (c v)))
    (degreeThreeFourBlockTwoSignSectionD8Map_matrix
      block P hr hs hcomponent hbinary htwo N x)
  change
    (Matrix.GeneralLinearGroup.toLin' b
        (DegreeSixS3Wreath.standardD8LinearMap (d x))).toLinearEquiv
        (g.toLinearEquiv (c v)) =
      (Matrix.GeneralLinearGroup.toLin' b
        (D.conjugator * phi x * D.conjugator⁻¹)).toLinearEquiv
        (g.toLinearEquiv (c v)) at hm
  rw [DegreeSixS3Wreath.standardD8LinearMap_toLin_apply] at hm
  have hcancel :
      g.toLinearEquiv⁻¹ (g.toLinearEquiv (c v)) = c v := by
    change g.toLinearEquiv.symm (g.toLinearEquiv (c v)) = c v
    exact g.toLinearEquiv.symm_apply_apply (c v)
  change
    (Matrix.GeneralLinearGroup.toLin' b D.conjugator).toLinearEquiv⁻¹
        ((Matrix.GeneralLinearGroup.toLin' b D.conjugator).toLinearEquiv
          (c v)) = c v at hcancel
  simp only [map_mul, map_inv,
    LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_inv,
    LinearEquiv.mul_apply] at hm
  rw [hcancel] at hm
  simpa only [degreeThreeFourBlockTwoSignSectionTernaryEquiv,
    c, D, b, g, phi, d, AddEquiv.trans_apply,
    map_mul, map_inv,
    LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_inv,
    LinearEquiv.mul_apply, hc] using hm.symm

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
  change Nat.card (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
    degreeThreeFourBlockTwoSignSectionAxis block P N)) ≤ 32 at htop
  have himage :=
    degreeThreeFourBlockTwoSignSectionLinearRange_card_eq_eight
      block P hr hs hcomponent hbinary htwo N
  change Nat.card phi.range = 8 at himage
  have hcard := phi.ker.card_mul_index
  rw [Subgroup.index_ker, himage] at hcard
  change Nat.card phi.ker ≤ 4
  omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
