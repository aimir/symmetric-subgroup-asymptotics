import SymmetricSubgroupAsymptotics.LinearJointMotionSubspaceMinBound
import SymmetricSubgroupAsymptotics.AbelianExtensionJointMotionClassBound
import Mathlib.RepresentationTheory.Basic

/-! A combined joint minimum for ORIGINAL nonsplit abelian extensions.
The actual normal kernel has an equivariant linear coordinate chart and
an actual invariant embedding in an ambient module. Both members of each
commuting pair belong to the SAME original quotient. The ambient action
may be signed/monomial; it is not replaced by an unsigned permutation
module. No class budget, splitting or independent maximum is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianExtensionLinearJointMinClassBound
open AbelianActionClassBound AbelianActionCommutingFibreBound
open AbelianJointMotionFibres LinearJointMotionFixedDual

variable {K W V Q : Type*} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Q]

def pairExponent (_rho : Representation K Q W) (tau : Representation K Q V) (x y : Q) : ℕ :=
  min (Module.finrank K W)
    (Module.finrank K (LinearJointMotionFixedDual.jointMotion (tau x) (tau y)).dualMap.ker+
      (Module.finrank K V-Module.finrank K W))

/-- The actual commuting quotient pairs are summed AFTER taking the
subspace/ambient minimum separately at each pair. -/
def combinedCapacity [Finite Q] (rho : Representation K Q W) (tau : Representation K Q V) : ℕ :=
  letI : Fintype (CommutingPairs Q) := Fintype.ofFinite _
  ∑ t : CommutingPairs Q, Nat.card K^pairExponent rho tau t.val.1 t.val.2

variable {N : Type*} [CommGroup N] [Finite N]
    (phi : Q →* MulAut N) (e : Multiplicative W ≃* N)
    (rho : Representation K Q W) (tau : Representation K Q V)
    (hcoord : ∀ q w, phi q (e (Multiplicative.ofAdd w))=
      e (Multiplicative.ofAdd (rho q w)))

include hcoord

private theorem motion_coordinates (q : Q) (a : N) :
    FrobeniusAbelianMotion.motion (phi q) a=
      e (Multiplicative.ofAdd (rho q (e.symm a).toAdd-(e.symm a).toAdd)) := by
  have hm (w : W) : FrobeniusAbelianMotion.motion (phi q) (e (Multiplicative.ofAdd w))=
      e (Multiplicative.ofAdd (rho q w-w)) := by
    change phi q (e (Multiplicative.ofAdd w))*(e (Multiplicative.ofAdd w))⁻¹=_
    rw [hcoord]
    simp only [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv]
  simpa only [ofAdd_toAdd,e.apply_symm_apply] using hm (e.symm a).toAdd

private theorem fibre_condition (x y : Q) (hxy : Commute x y) (a b : N) :
    Commute (⟨a,x⟩ : N ⋊[phi] Q) (⟨b,y⟩ : N ⋊[phi] Q) ↔
      LinearJointMotionFixedDual.jointMotion (rho x) (rho y)
        ((e.symm b).toAdd,(e.symm a).toAdd)=0 := by
  rw [commute_iff_motion_eq phi x y hxy,motion_coordinates phi e rho hcoord,
    motion_coordinates phi e rho hcoord]
  constructor
  · intro h
    have he : rho x (e.symm b).toAdd-(e.symm b).toAdd=
        rho y (e.symm a).toAdd-(e.symm a).toAdd :=
      Multiplicative.ofAdd.injective (e.injective h)
    simpa only [LinearJointMotionFixedDual.jointMotion,LinearMap.coprod_apply,
      LinearMap.sub_apply,LinearMap.id_apply,LinearMap.neg_apply,←sub_eq_add_neg] using
      sub_eq_zero.mpr he
  · intro h
    have he : rho x (e.symm b).toAdd-(e.symm b).toAdd=
        rho y (e.symm a).toAdd-(e.symm a).toAdd := sub_eq_zero.mp (by
      simpa only [LinearJointMotionFixedDual.jointMotion,LinearMap.coprod_apply,
        LinearMap.sub_apply,LinearMap.id_apply,LinearMap.neg_apply,←sub_eq_add_neg] using h)
    exact congrArg (fun w : W => e (Multiplicative.ofAdd w)) he

private def fibreEquivKernel (x y : Q) (hxy : Commute x y) :
    Fibre phi x y ≃ (LinearJointMotionFixedDual.jointMotion (rho x) (rho y)).ker where
  toFun p := ⟨((e.symm p.val.2).toAdd,(e.symm p.val.1).toAdd),
    (fibre_condition phi e rho hcoord x y hxy p.val.1 p.val.2).mp p.property⟩
  invFun p := ⟨(e (Multiplicative.ofAdd p.val.2),e (Multiplicative.ofAdd p.val.1)),by
    apply (fibre_condition phi e rho hcoord x y hxy _ _).mpr
    simpa only [e.symm_apply_apply] using p.property⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (e.apply_symm_apply p.val.1) (e.apply_symm_apply p.val.2)
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext
      (congrArg Multiplicative.toAdd (e.symm_apply_apply (Multiplicative.ofAdd p.val.1)))
      (congrArg Multiplicative.toAdd (e.symm_apply_apply (Multiplicative.ofAdd p.val.2)))

/-- A bound for each actual commuting fibre, before summing. No
independent fixed-space maximum is substituted. -/
theorem fibre_card_le_min (f : W →ₗ[K] V) (hf : Function.Injective f)
    (hintertwine : ∀ q w, f (rho q w)=tau q (f w))
    (x y : Q) (hxy : Commute x y) :
    Nat.card (Fibre phi x y)≤Nat.card N*Nat.card K^pairExponent rho tau x y := by
  rw [Nat.card_congr (fibreEquivKernel phi e rho hcoord x y hxy)]
  have hN : Nat.card N=Nat.card W :=
    (Nat.card_congr e.symm.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  rw [hN]
  exact LinearJointMotionSubspaceMinBound.card_kernel_le_min f hf
    (rho x) (rho y) (tau x) (tau y) (hintertwine x) (hintertwine y)

omit hcoord

section OriginalExtension
variable {G : Type*} [Group G] [Finite G] (A : Subgroup G) [A.Normal] [IsMulCommutative A]

/-- Actual quotient conjugation is retained. The linear coordinates and
ambient embedding are structural data, not a fitted capacity or a split
extension assertion. This applies equally to signed ternary coordinates. -/
theorem nonsplit_class_card_mul_quotient_le
    (eA : Multiplicative W ≃* A)
    (rhoA : Representation K (G ⧸ A) W) (tauA : Representation K (G ⧸ A) V)
    (hcoordA : ∀ q w, AbelianExtensionConjugation.quotientConjugation A q
      (eA (Multiplicative.ofAdd w))=eA (Multiplicative.ofAdd (rhoA q w)))
    (f : W →ₗ[K] V) (hf : Function.Injective f)
    (hintertwine : ∀ q w, f (rhoA q w)=tauA q (f w)) :
    Nat.card (G ⧸ A)*Nat.card (ConjClasses G)≤combinedCapacity rhoA tauA := by
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm' }
  let phiA := AbelianExtensionConjugation.quotientConjugation A
  have hindex (t : CommutingPairs (G ⧸ A)) :
      (AbelianJointMotionFibres.jointMotion phiA t.val.1 t.val.2).range.index≤
        Nat.card K^pairExponent rhoA tauA t.val.1 t.val.2 := by
    have hh := fibre_card_le_min phiA eA rhoA tauA hcoordA f hf hintertwine
      t.val.1 t.val.2 t.property
    rw [commuting_fibre_card phiA t.val.1 t.val.2 t.property] at hh
    exact Nat.le_of_mul_le_mul_left hh (Nat.card_pos (α:=A))
  have hactual := AbelianExtensionJointMotionClassBound.class_card_mul_quotient_le A
  apply hactual.trans
  change AbelianExtensionJointMotionClassBound.jointCapacity phiA≤combinedCapacity rhoA tauA
  letI : Fintype (CommutingPairs (G ⧸ A)) := Fintype.ofFinite _
  change (∑ t : CommutingPairs (G ⧸ A),
      (AbelianJointMotionFibres.jointMotion phiA t.val.1 t.val.2).range.index)≤
    ∑ t : CommutingPairs (G ⧸ A), Nat.card K^pairExponent rhoA tauA t.val.1 t.val.2
  exact Finset.sum_le_sum (fun t _ => hindex t)

end OriginalExtension
end SymmetricSubgroupAsymptotics.AbelianExtensionLinearJointMinClassBound
