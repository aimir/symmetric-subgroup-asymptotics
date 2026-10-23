import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedPositiveProjection
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRootFamilyCover
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
import SymmetricSubgroupAsymptotics.CFSGExceptionalRootCountBound

/-! Genuine fixed root lines, restricted inside J, map to the ORIGINAL
simple twisted E6 model. The actual finite relative-root menu and fixed
upper conjugators survive this map without a source-faithfulness premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootFamily
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckFixedPositiveProjection
open CFSGTwistedE6GeckFixedRootFamilyCover CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckFixedRangePreimage CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGTwistedE6OriginalGoodSylow
open CFSGTwistedE6GeckImagePositiveSylow CFSGTwistedE6GeckSourceAction
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoRootPairing
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGIntegerMatrixPairing CFSGSerreOrdinaryTwists CFSGTwistedE6FixedA2
open CFSGSubgroupConjugateRestriction
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def rootLineInGenerated (q : CFSG.PrimePower) (k : Roots A) :
    Subgroup (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) :=
  (fixedRootLine (q.Extension 2) (definingFieldAutomorphism q 2) k).subgroupOf
    (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2))

def originalRootLine (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (k : Roots A) : Subgroup (CFSG.Models.TwistedE6 q) :=
  (rootLineInGenerated q k).map (generatedToOriginal q)

theorem positive_fixed_line_le_generated (q : CFSG.PrimePower) (theta : Roots A)
    (htheta : ∀i,0≤theta.val i) :
    fixedRootLine (q.Extension 2) (definingFieldAutomorphism q 2) theta≤
      fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2) := by
  intro x hx
  exact signedFixed_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) false
    ⟨positive_root_subgroup_le A hd hs hp ho (q.Extension 2) theta htheta hx.1,hx.2⟩

theorem originalRootLine_le_positiveSylow (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (theta : Roots A) (htheta : ∀i,0≤theta.val i) :
    originalRootLine q theta≤(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) := by
  rintro _ ⟨j,hj,rfl⟩
  have hsign : j∈rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false :=
    ⟨positive_root_subgroup_le A hd hs hp ho (q.Extension 2) theta htheta hj.1,hj.2⟩
  change generatedToOriginal q j∈(imagePositiveSylow q : Subgroup _).map (imageToOriginal q)
  refine ⟨generatedToDerived q j,?_,rfl⟩
  rw [imagePositiveSylow_coe]
  exact ⟨j,hsign,rfl⟩

theorem originalRootLine_ne_top (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (theta : Roots A) (htheta : ∀i,0≤theta.val i) :
    originalRootLine q theta≠⊤ := by
  intro htop
  apply originalPositiveSylow_ne_top q
  apply top_unique
  rw [←htop]
  exact originalRootLine_le_positiveSylow q theta htheta

theorem fixedPositiveToOriginal_apply (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (u : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false) :
    fixedPositiveToOriginal q u=generatedToOriginal q (fixedPositiveToGenerated q u) := rfl

private theorem restrict_conjugate_equality {G : Type*} [Group G]
    (H R S : Subgroup G) (hR : R≤H) (hS : S≤H) (g u : H)
    (he : R.map (MulAut.conj g.val).toMonoidHom=S.map (MulAut.conj u.val).toMonoidHom) :
    (R.subgroupOf H).map (MulAut.conj g).toMonoidHom=
      (S.subgroupOf H).map (MulAut.conj u).toMonoidHom := by
  apply Subgroup.map_injective (f:=H.subtype) H.subtype_injective
  rw [map_conjugate,map_conjugate,Subgroup.map_subgroupOf_eq_of_le hR,
    Subgroup.map_subgroupOf_eq_of_le hS]
  exact he

private theorem push_conjugate_equality {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (R S : Subgroup G) (g u : G)
    (he : R.map (MulAut.conj g).toMonoidHom=S.map (MulAut.conj u).toMonoidHom) :
    (R.map f).map (MulAut.conj (f g)).toMonoidHom=
      (S.map f).map (MulAut.conj (f u)).toMonoidHom := by
  exact (map_conjugate f R g).symm.trans
    ((congrArg (fun T : Subgroup G=>T.map f) he).trans (map_conjugate f S u))

theorem original_fixed_root_family_cover (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (theta : Roots A) (htheta : ∀i,0≤theta.val i)
    (hdom : ∀i,0 ≤ integerPairing A theta.val (Pi.single i (1 : ℤ) : Fin 6→ℤ))
    (g : CFSG.Models.TwistedE6 q) :
    ∃k : relativeRootMenu theta,
      ∃u : signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false,
        (originalRootLine q theta).map (MulAut.conj g).toMonoidHom=
          (originalRootLine q k.val).map (MulAut.conj (fixedPositiveToOriginal q u)).toMonoidHom := by
  obtain ⟨j,hj⟩ := generatedToOriginal_surjective q g
  obtain ⟨k,u,he⟩ := fixed_conjugate_eq_fixed_positive_conjugate (q.Extension 2)
    (definingFieldAutomorphism q 2) theta htheta hdom j.val
    (fixedRootGenerated_le_matrixGroup (q.Extension 2) (definingFieldAutomorphism q 2) j.property)
    (fixedRootGenerated_le_fixed (q.Extension 2) (definingFieldAutomorphism q 2) j.property)
  let uj := fixedPositiveToGenerated q u
  have hr := restrict_conjugate_equality
    (fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)) _ _
    (positive_fixed_line_le_generated q theta htheta)
    (fixedRootLine_le_generated (q.Extension 2) (definingFieldAutomorphism q 2) theta htheta k)
    j uj he
  have hm := push_conjugate_equality (generatedToOriginal q)
    (rootLineInGenerated q theta) (rootLineInGenerated q k.val) j uj hr
  refine ⟨k,u,?_⟩
  calc
    _=(originalRootLine q theta).map (MulAut.conj (generatedToOriginal q j)).toMonoidHom :=
      congrArg (fun z=>(originalRootLine q theta).map (MulAut.conj z).toMonoidHom) hj.symm
    _=(originalRootLine q k.val).map (MulAut.conj (generatedToOriginal q uj)).toMonoidHom := hm
    _=_ := congrArg (fun z=>(originalRootLine q k.val).map (MulAut.conj z).toMonoidHom)
      (fixedPositiveToOriginal_apply q u).symm

theorem original_root_menu_card_le (theta : Roots A) : Nat.card (relativeRootMenu theta)≤512 :=
  (relativeRootMenu_card_le theta).trans CFSGExceptionalRootCountBound.E6_root_card_le

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootFamily
