import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSymmetricSixActions
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators

/-! The faithful six-edge action of S4 times the opposite-edge involution.
Projection is an actual homomorphism with kernel of cardinal two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImage
open TwelvePointRemainingStructuralSymmetricSixActions (opposite opposite_square opposite_edge_commute)
open SymmetricFourTwelvePointSocles (edge)
abbrev Group := Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2)

def complement : Equiv.Perm (Fin 2) →* Equiv.Perm (Fin 6) where
  toFun z := if z=1 then 1 else opposite
  map_one' := by simp
  map_mul' := by
    have h : ∀ z w : Equiv.Perm (Fin 2),
        (if z*w=1 then (1 : Equiv.Perm (Fin 6)) else opposite)=
          (if z=1 then 1 else opposite)*(if w=1 then 1 else opposite) := by decide +kernel
    exact h

theorem complement_edge_commute (z : Equiv.Perm (Fin 2)) (g : Equiv.Perm (Fin 4)) :
    Commute (complement z) (edge g) := by
  change Commute (if z=1 then 1 else opposite) (edge g)
  split
  · exact Commute.one_left _
  · exact opposite_edge_commute g

def action : Group →* Equiv.Perm (Fin 6) where
  toFun g := edge g.1 * complement g.2
  map_one' := by simp
  map_mul' g h := by
    change edge (g.1*h.1)*complement (g.2*h.2)=_
    rw [map_mul,map_mul]
    have hc := (complement_edge_commute g.2 h.1).eq.symm
    calc
      (edge g.1*edge h.1)*(complement g.2*complement h.2)=
          edge g.1*(edge h.1*complement g.2)*complement h.2 := by group
      _=edge g.1*(complement g.2*edge h.1)*complement h.2 := by rw [hc]
      _=(edge g.1*complement g.2)*(edge h.1*complement h.2) := by group

theorem action_injective : Function.Injective action := by
  have h : ∀ g h : Group, (∀ i : Fin 6, action g i=action h i) → g=h := by
    decide +kernel
  exact fun _ _ he => h _ _ (fun i => congrArg (fun p : Equiv.Perm (Fin 6) => p i) he)

def canonicalEquiv : Group ≃* action.range :=
  MulEquiv.ofBijective action.rangeRestrict
    ⟨fun _ _ h => action_injective (congrArg Subtype.val h),action.rangeRestrict_surjective⟩

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (himage : F.top.range=action.range)
def equiv : F.top.range ≃* Group :=
  (MulEquiv.subgroupCongr himage).trans canonicalEquiv.symm

def topProjection : F.top.range →* Equiv.Perm (Fin 4) :=
  (MonoidHom.fst _ _).comp (equiv F himage).toMonoidHom

theorem topProjection_surjective : Function.Surjective (topProjection F himage) := by
  intro g
  exact ⟨(equiv F himage).symm (g,1),by simp [topProjection]⟩

include himage in
theorem top_card : Nat.card F.top.range=48 := by
  rw [Nat.card_congr (equiv F himage).toEquiv,Nat.card_prod,Nat.card_perm,
    Nat.card_perm,Nat.card_fin,Nat.card_fin]
  decide

theorem topProjection_kernel_card : Nat.card (topProjection F himage).ker=2 := by
  have hquot : Nat.card (F.top.range ⧸ (topProjection F himage).ker)=24 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (topProjection F himage) (topProjection_surjective F himage)).toEquiv]
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (topProjection F himage).ker
  rw [top_card F himage,hquot] at h
  omega
end SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImage
