import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignBottomPairKernelFaithful
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSectionTopLowerBound
import SymmetricSubgroupAsymptotics.TernaryPlaneKleinNormalizer

/-!
# The rank-two bottom linear image

When the full translation layer has ternary rank two, the signed quotient
acts on a ternary plane.  Its literal pair kernel embeds as a normal Klein
four subgroup of the matrix image, and a sign-class exchanger survives
outside that subgroup.  The image therefore has order eight and is
conjugate to the standard monomial `D8` action.
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

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- The literal signed action relabelled back onto the actual quotient. -/
def degreeThreeFourBlockTwoSignBottomSignedTopHom
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    (degreeThreeFourBlockPairChart block P hr hs hcomponent).action →*
      G ⧸ E block P :=
  (degreeThreeFourBlockPairChart
    block P hr hs hcomponent).sourceEquiv.symm.toMonoidHom

theorem degreeThreeFourBlockTwoSignBottomSignedTopHom_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignBottomSignedTopHom
        block P hr hs hcomponent) :=
  (degreeThreeFourBlockPairChart
    block P hr hs hcomponent).sourceEquiv.symm.surjective

/-- Restriction of the signed-top relabelling to the literal pair kernel. -/
def degreeThreeFourBlockTwoSignBottomPairKernelTopHom
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    C.frame.top.ker →* G ⧸ E block P := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  exact C.sourceEquiv.symm.toMonoidHom.comp C.frame.top.ker.subtype

@[simp] theorem degreeThreeFourBlockTwoSignBottomSignedTopHom_pairKernel
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (k : (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker) :
    degreeThreeFourBlockTwoSignBottomSignedTopHom
        block P hr hs hcomponent k.1 =
      degreeThreeFourBlockTwoSignBottomPairKernelTopHom
        block P hr hs hcomponent k := rfl

/-- Matrix realization of the signed quotient action on the rank-two full
translation layer. -/
noncomputable def degreeThreeFourBlockTwoSignBottomLinearMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    (G ⧸ E block P) →* LinearThree.GL3 := by
  let V := TranslationSubmodule block P
  let basis : Module.Basis (Fin 2) (ZMod P.p) V :=
    Module.finBasisOfFinrankEq (ZMod P.p) V hfin
  let rho := (elementaryChart block P).quotientRepresentation.ρ
  let phi0 : (G ⧸ E block P) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod P.p) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      (Representation.asGroupHom rho)
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  let e : ZMod P.p ≃+* ZMod 3 := ZMod.ringEquivCongr hp
  exact (Matrix.GeneralLinearGroup.map e.toRingHom).comp phi0

/-- Additive coordinates on the rank-two translation layer, chosen in sync
with its matrix realization. -/
noncomputable def degreeThreeFourBlockTwoSignBottomCoordinateEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    TranslationSubmodule block P ≃+
      DegreeSixS3Wreath.TernaryPlane := by
  let V := TranslationSubmodule block P
  let basis : Module.Basis (Fin 2) (ZMod P.p) V :=
    Module.finBasisOfFinrankEq (ZMod P.p) V hfin
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  let e : ZMod P.p ≃+* ZMod 3 := ZMod.ringEquivCongr hp
  exact basis.equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ : Fin 2 => e.toAddEquiv)

/-- The chosen bottom coordinates realize quotient conjugation by the
exported matrix. -/
theorem degreeThreeFourBlockTwoSignBottomCoordinateEquiv_action
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (x : G ⧸ E block P)
    (v : TranslationSubmodule block P) :
    degreeThreeFourBlockTwoSignBottomCoordinateEquiv
        block P hr hs hcomponent hfin
        ((elementaryChart block P).quotientRepresentation.ρ x v) =
      (Matrix.GeneralLinearGroup.toLin'
        (Pi.basisFun (ZMod 3) (Fin 2))
          (degreeThreeFourBlockTwoSignBottomLinearMap
            block P hr hs hcomponent hfin x)).toLinearEquiv
        (degreeThreeFourBlockTwoSignBottomCoordinateEquiv
          block P hr hs hcomponent hfin v) := by
  let V := TranslationSubmodule block P
  let basis : Module.Basis (Fin 2) (ZMod P.p) V :=
    Module.finBasisOfFinrankEq (ZMod P.p) V hfin
  let rho := (elementaryChart block P).quotientRepresentation.ρ
  let phi0 : (G ⧸ E block P) →*
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

/-- Equality of bottom matrices reflects equality of the original quotient
operators. -/
theorem degreeThreeFourBlockTwoSignBottomLinearMap_reflects
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (x y : G ⧸ E block P)
    (hxy : degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin x =
      degreeThreeFourBlockTwoSignBottomLinearMap
        block P hr hs hcomponent hfin y) :
    (elementaryChart block P).quotientRepresentation.ρ x =
      (elementaryChart block P).quotientRepresentation.ρ y := by
  let V := TranslationSubmodule block P
  let basis : Module.Basis (Fin 2) (ZMod P.p) V :=
    Module.finBasisOfFinrankEq (ZMod P.p) V hfin
  let rho := (elementaryChart block P).quotientRepresentation.ρ
  let phi0 : (G ⧸ E block P) →*
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
    simpa only [degreeThreeFourBlockTwoSignBottomLinearMap, phi0, e,
      MonoidHom.comp_apply] using hij
  have hrho : Representation.asGroupHom rho x =
      Representation.asGroupHom rho y := by
    apply (Matrix.GeneralLinearGroup.toLin' basis).symm.injective
    simpa only [phi0, MonoidHom.comp_apply] using hphi0
  exact congrArg Units.val hrho

/-- Restriction of the bottom matrix action to the literal pair kernel. -/
def degreeThreeFourBlockTwoSignBottomPairLinearMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    (degreeThreeFourBlockPairChart
      block P hr hs hcomponent).frame.top.ker →* LinearThree.GL3 :=
  (degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin).comp
      (degreeThreeFourBlockTwoSignBottomPairKernelTopHom
        block P hr hs hcomponent)

/-- The bottom pair-kernel matrix map with standard `C₂²` source. -/
def degreeThreeFourBlockTwoSignBottomPairBitsLinearMap
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →*
      LinearThree.GL3 :=
  (degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin).comp
      (degreeThreeFourBlockTwoSign_pairKernelEquiv
        block P hr hs hcomponent htwo).symm.toMonoidHom

theorem degreeThreeFourBlockTwoSignBottomPairLinearMap_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Function.Injective
      (degreeThreeFourBlockTwoSignBottomPairLinearMap
        block P hr hs hcomponent hfin) := by
  intro x y hxy
  apply degreeThreeFourBlockTwoSignBottomPairKernelRepresentation_injective
    block P hr hs hcomponent hbinary
  exact degreeThreeFourBlockTwoSignBottomLinearMap_reflects
    block P hr hs hcomponent hfin _ _ hxy

theorem degreeThreeFourBlockTwoSignBottomPairBitsLinearMap_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Function.Injective
      (degreeThreeFourBlockTwoSignBottomPairBitsLinearMap
        block P hr hs hcomponent htwo hfin) :=
  (degreeThreeFourBlockTwoSignBottomPairLinearMap_injective
    block P hr hs hcomponent hbinary hfin).comp
      (degreeThreeFourBlockTwoSign_pairKernelEquiv
        block P hr hs hcomponent htwo).symm.injective

theorem degreeThreeFourBlockTwoSignBottomPairBitsLinearMap_range
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    (degreeThreeFourBlockTwoSignBottomPairBitsLinearMap
      block P hr hs hcomponent htwo hfin).range =
      (degreeThreeFourBlockTwoSignBottomPairLinearMap
        block P hr hs hcomponent hfin).range := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨(degreeThreeFourBlockTwoSign_pairKernelEquiv
      block P hr hs hcomponent htwo).symm x, rfl⟩
  · rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSign_pairKernelEquiv
      block P hr hs hcomponent htwo k, by
        simp only [degreeThreeFourBlockTwoSignBottomPairBitsLinearMap,
          MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.symm_apply_apply]⟩

/-- The bottom matrix pair-kernel image has order four. -/
theorem degreeThreeFourBlockTwoSignBottomPairLinearRange_card
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card (degreeThreeFourBlockTwoSignBottomPairLinearMap
      block P hr hs hcomponent hfin).range = 4 := by
  let f := degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin
  calc
    Nat.card f.range = Nat.card
        (degreeThreeFourBlockPairChart
          block P hr hs hcomponent).frame.top.ker :=
      Nat.card_congr
        (MonoidHom.ofInjective
          (degreeThreeFourBlockTwoSignBottomPairLinearMap_injective
            block P hr hs hcomponent hbinary hfin)).toEquiv.symm
    _ = 4 := degreeThreeFourBlockTwoSign_pairKernel_card
      block P hr hs hcomponent htwo

/-- Every element in the bottom matrix pair-kernel image has square one. -/
theorem degreeThreeFourBlockTwoSignBottomPairLinearRange_square
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (z : (degreeThreeFourBlockTwoSignBottomPairLinearMap
      block P hr hs hcomponent hfin).range) :
    z ^ 2 = 1 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let f := degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin
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

private theorem degreeThreeFourBlockTwoSignBottomPairTopRange_normal
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    (degreeThreeFourBlockTwoSignBottomPairKernelTopHom
      block P hr hs hcomponent).range.Normal := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let f := degreeThreeFourBlockTwoSignBottomSignedTopHom
    block P hr hs hcomponent
  let K := C.frame.top.ker
  have hf : Function.Surjective f :=
    degreeThreeFourBlockTwoSignBottomSignedTopHom_surjective
      block P hr hs hcomponent
  have hnormal : (K.map f).Normal :=
    Subgroup.Normal.map (show K.Normal from inferInstance) f hf
  have heq : K.map f =
      (degreeThreeFourBlockTwoSignBottomPairKernelTopHom
        block P hr hs hcomponent).range := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k.1, k.2, rfl⟩
  rw [← heq]
  exact hnormal

/-- The bottom matrix pair-kernel image is normal in the full matrix
image. -/
theorem degreeThreeFourBlockTwoSignBottomPairLinearRange_normal
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    let phi := degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin
    let psi := degreeThreeFourBlockTwoSignBottomPairLinearMap
      block P hr hs hcomponent hfin
    (psi.range.subgroupOf phi.range).Normal := by
  let phi := degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin
  let psi := degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin
  let L := (degreeThreeFourBlockTwoSignBottomPairKernelTopHom
    block P hr hs hcomponent).range
  have hL : L.Normal :=
    degreeThreeFourBlockTwoSignBottomPairTopRange_normal
      block P hr hs hcomponent
  have hle : psi.range ≤ phi.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSignBottomPairKernelTopHom
      block P hr hs hcomponent k, rfl⟩
  apply (Subgroup.normal_subgroupOf_iff hle).mpr
  intro k h hk hh
  obtain ⟨x, hx⟩ := hk
  obtain ⟨t, ht⟩ := hh
  have hxL : degreeThreeFourBlockTwoSignBottomPairKernelTopHom
      block P hr hs hcomponent x ∈ L := ⟨x, rfl⟩
  have hconj := hL.conj_mem _ hxL t
  obtain ⟨y, hy⟩ := hconj
  refine ⟨y, ?_⟩
  rw [← hx, ← ht]
  simp only [psi, degreeThreeFourBlockTwoSignBottomPairLinearMap,
    MonoidHom.comp_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg phi hy

/-- The full bottom matrix image has order at most eight. -/
theorem degreeThreeFourBlockTwoSignBottomLinearRange_card_le_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card (degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin).range ≤ 8 := by
  let phi := degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin
  let psi := degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin
  let f := degreeThreeFourBlockTwoSignBottomPairBitsLinearMap
    block P hr hs hcomponent htwo hfin
  have hfrange : f.range = psi.range :=
    degreeThreeFourBlockTwoSignBottomPairBitsLinearMap_range
      block P hr hs hcomponent htwo hfin
  have hle : psi.range ≤ phi.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSignBottomPairKernelTopHom
      block P hr hs hcomponent k, rfl⟩
  have hfle : f.range ≤ phi.range := hfrange.trans_le hle
  have hfnormal : (f.range.subgroupOf phi.range).Normal := by
    rw [hfrange]
    exact degreeThreeFourBlockTwoSignBottomPairLinearRange_normal
      block P hr hs hcomponent hfin
  exact LinearThree.card_le_eight_of_normalizes_kleinRange
    phi.range f
      (degreeThreeFourBlockTwoSignBottomPairBitsLinearMap_injective
        block P hr hs hcomponent hbinary htwo hfin)
      hfle hfnormal

/-- A sign-class exchanger has bottom matrix image outside the Klein
pair-kernel image. -/
theorem degreeThreeFourBlockTwoSignBottom_exists_linear_outside_pairRange
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    ∃ u : (degreeThreeFourBlockPairChart
        block P hr hs hcomponent).action,
      degreeThreeFourBlockTwoSignBottomLinearMap
          block P hr hs hcomponent hfin
          (degreeThreeFourBlockTwoSignBottomSignedTopHom
            block P hr hs hcomponent u) ∉
        (degreeThreeFourBlockTwoSignBottomPairLinearMap
          block P hr hs hcomponent hfin).range := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  let F := C.frame
  let phi := degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin
  let f := degreeThreeFourBlockTwoSignBottomSignedTopHom
    block P hr hs hcomponent
  let psi := degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin
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
    (degreeThreeFourBlockTwoSignBottomPairLinearMap_injective
      block P hr hs hcomponent hbinary hfin hconjMap)

/-- The rank-two bottom matrix image is an order-eight binary subgroup of
`GL₂(3)`. -/
theorem degreeThreeFourBlockTwoSignBottomLinearRange_card_eq_eight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card (degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin).range = 8 := by
  let phi := degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin
  let psi := degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin
  let K := psi.range.subgroupOf phi.range
  have hKcard : Nat.card K = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
      rintro _ ⟨k, rfl⟩
      exact ⟨degreeThreeFourBlockTwoSignBottomPairKernelTopHom
        block P hr hs hcomponent k, rfl⟩)).toEquiv]
    exact degreeThreeFourBlockTwoSignBottomPairLinearRange_card
      block P hr hs hcomponent hbinary htwo hfin
  obtain ⟨u, hu⟩ :=
    degreeThreeFourBlockTwoSignBottom_exists_linear_outside_pairRange
      block P hr hs hcomponent hbinary htwo hfin
  have hKne : K ≠ ⊤ := by
    intro htop
    apply hu
    change phi (degreeThreeFourBlockTwoSignBottomSignedTopHom
      block P hr hs hcomponent u) ∈ psi.range
    have hmem : (⟨phi (degreeThreeFourBlockTwoSignBottomSignedTopHom
      block P hr hs hcomponent u), ⟨_, rfl⟩⟩ : phi.range) ∈ K := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  have hindex : 1 < K.index := Subgroup.one_lt_index_of_ne_top hKne
  have hcard := K.card_mul_index
  have hupper := degreeThreeFourBlockTwoSignBottomLinearRange_card_le_eight
    block P hr hs hcomponent hbinary htwo hfin
  change Nat.card phi.range ≤ 8 at hupper
  rw [hKcard] at hcard
  have hlower : 8 ≤ Nat.card phi.range := by
    calc
      8 = 4 * 2 := by norm_num
      _ ≤ 4 * K.index := Nat.mul_le_mul_left 4 (by omega)
      _ = Nat.card phi.range := hcard
  change Nat.card phi.range = 8
  omega

/-- Change of basis carrying the exact bottom matrix image to the standard
monomial `D8`. -/
noncomputable def degreeThreeFourBlockTwoSignBottomLinearRangeD8Conjugacy
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    LinearThree.SubgroupD8Conjugacy
      (degreeThreeFourBlockTwoSignBottomLinearMap
        block P hr hs hcomponent hfin).range := by
  let phi := degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin
  let psi := degreeThreeFourBlockTwoSignBottomPairLinearMap
    block P hr hs hcomponent hfin
  let f := degreeThreeFourBlockTwoSignBottomPairBitsLinearMap
    block P hr hs hcomponent htwo hfin
  have hfrange : f.range = psi.range :=
    degreeThreeFourBlockTwoSignBottomPairBitsLinearMap_range
      block P hr hs hcomponent htwo hfin
  have hle : psi.range ≤ phi.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨degreeThreeFourBlockTwoSignBottomPairKernelTopHom
      block P hr hs hcomponent k, rfl⟩
  have hfle : f.range ≤ phi.range := hfrange.trans_le hle
  have hfnormal : (f.range.subgroupOf phi.range).Normal := by
    rw [hfrange]
    exact degreeThreeFourBlockTwoSignBottomPairLinearRange_normal
      block P hr hs hcomponent hfin
  exact
    LinearThree.subgroupD8Conjugacy_of_card_eight_of_normalizes_kleinRange
      phi.range f
        (degreeThreeFourBlockTwoSignBottomPairBitsLinearMap_injective
          block P hr hs hcomponent hbinary htwo hfin)
        hfle hfnormal
        (degreeThreeFourBlockTwoSignBottomLinearRange_card_eq_eight
          block P hr hs hcomponent hbinary htwo hfin)

/-- The actual signed quotient maps onto the standard dihedral group through
its order-eight matrix image. -/
noncomputable def degreeThreeFourBlockTwoSignBottomD8Map
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    (G ⧸ E block P) →* DegreeSixS3Wreath.D8 :=
  (degreeThreeFourBlockTwoSignBottomLinearRangeD8Conjugacy
      block P hr hs hcomponent hbinary htwo hfin).equiv.toMonoidHom.comp
    (degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin).rangeRestrict

theorem degreeThreeFourBlockTwoSignBottomD8Map_surjective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignBottomD8Map
        block P hr hs hcomponent hbinary htwo hfin) :=
  (degreeThreeFourBlockTwoSignBottomLinearRangeD8Conjugacy
      block P hr hs hcomponent hbinary htwo hfin).equiv.surjective.comp
    (degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin).rangeRestrict_surjective

/-- Matrix compatibility retained by the bottom dihedral quotient. -/
theorem degreeThreeFourBlockTwoSignBottomD8Map_matrix
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (x : G ⧸ E block P) :
    let D := degreeThreeFourBlockTwoSignBottomLinearRangeD8Conjugacy
      block P hr hs hcomponent hbinary htwo hfin
    DegreeSixS3Wreath.standardD8LinearMap
        (degreeThreeFourBlockTwoSignBottomD8Map
          block P hr hs hcomponent hbinary htwo hfin x) =
      D.conjugator *
        degreeThreeFourBlockTwoSignBottomLinearMap
          block P hr hs hcomponent hfin x *
        D.conjugator⁻¹ := by
  let D := degreeThreeFourBlockTwoSignBottomLinearRangeD8Conjugacy
    block P hr hs hcomponent hbinary htwo hfin
  exact D.matrix_eq
    ((degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin).rangeRestrict x)

/-- Coordinates on the rank-two bottom translation layer after the change
of basis putting its top action in standard monomial form. -/
noncomputable def degreeThreeFourBlockTwoSignBottomTernaryEquiv
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    TranslationSubmodule block P ≃+
      DegreeSixS3Wreath.TernaryPlane :=
  (degreeThreeFourBlockTwoSignBottomCoordinateEquiv
    block P hr hs hcomponent hfin).trans
      (Matrix.GeneralLinearGroup.toLin'
        (Pi.basisFun (ZMod 3) (Fin 2))
          (degreeThreeFourBlockTwoSignBottomLinearRangeD8Conjugacy
            block P hr hs hcomponent hbinary htwo hfin).conjugator
      ).toLinearEquiv.toAddEquiv

/-- The final bottom coordinates intertwine quotient conjugation with the
standard `D8` action on `C₃²`. -/
theorem degreeThreeFourBlockTwoSignBottomTernaryEquiv_action
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2)
    (x : G ⧸ E block P)
    (v : TranslationSubmodule block P) :
    degreeThreeFourBlockTwoSignBottomTernaryEquiv
        block P hr hs hcomponent hbinary htwo hfin
        ((elementaryChart block P).quotientRepresentation.ρ x v) =
      DegreeSixS3Wreath.monomialRepresentation
        (degreeThreeFourBlockTwoSignBottomD8Map
          block P hr hs hcomponent hbinary htwo hfin x)
        (degreeThreeFourBlockTwoSignBottomTernaryEquiv
          block P hr hs hcomponent hbinary htwo hfin v) := by
  let c := degreeThreeFourBlockTwoSignBottomCoordinateEquiv
    block P hr hs hcomponent hfin
  let D := degreeThreeFourBlockTwoSignBottomLinearRangeD8Conjugacy
    block P hr hs hcomponent hbinary htwo hfin
  let b := Pi.basisFun (ZMod 3) (Fin 2)
  let g := Matrix.GeneralLinearGroup.toLin' b D.conjugator
  let phi := degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin
  let d := degreeThreeFourBlockTwoSignBottomD8Map
    block P hr hs hcomponent hbinary htwo hfin
  have hc := degreeThreeFourBlockTwoSignBottomCoordinateEquiv_action
    block P hr hs hcomponent hfin x v
  have hm := congrArg
    (fun A : LinearThree.GL3 =>
      (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv
        (g.toLinearEquiv (c v)))
    (degreeThreeFourBlockTwoSignBottomD8Map_matrix
      block P hr hs hcomponent hbinary htwo hfin x)
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
  simpa only [degreeThreeFourBlockTwoSignBottomTernaryEquiv,
    c, D, b, g, phi, d, AddEquiv.trans_apply,
    map_mul, map_inv,
    LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    LinearMap.GeneralLinearGroup.toLinearEquiv_inv,
    LinearEquiv.mul_apply, hc] using hm.symm

/-- The residual kernel above the bottom `D8` matrix image has order at
most four. -/
theorem degreeThreeFourBlockTwoSignBottomLinearMap_kernel_card_le_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfin : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 2) :
    Nat.card (degreeThreeFourBlockTwoSignBottomLinearMap
      block P hr hs hcomponent hfin).ker ≤ 4 := by
  let phi := degreeThreeFourBlockTwoSignBottomLinearMap
    block P hr hs hcomponent hfin
  have htop : Nat.card (G ⧸ E block P) ≤ 32 := by
    rcases degreeThreeFourBlockTwoSign_signedQuotient_card_cases
      block P hr hs hcomponent hbinary htwo with h16 | h32
    · rw [h16]
      norm_num
    · rw [h32]
  have himage :=
    degreeThreeFourBlockTwoSignBottomLinearRange_card_eq_eight
      block P hr hs hcomponent hbinary htwo hfin
  have hcard := phi.ker.card_mul_index
  rw [Subgroup.index_ker, himage] at hcard
  change Nat.card phi.ker ≤ 4
  omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
