import SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImage
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImageConjugate
open DoubleSymmetricFourSixImage (Group action action_injective)
def model (labels : Equiv.Perm (Fin 6)) : Group →* Equiv.Perm (Fin 6) :=
  (MulAut.conj labels.symm).toMonoidHom.comp action

def modelEquiv (labels : Equiv.Perm (Fin 6)) : Group ≃* (model labels).range :=
  MulEquiv.ofBijective (model labels).rangeRestrict
    ⟨fun _ _ h => action_injective ((MulAut.conj labels.symm).injective
      (congrArg Subtype.val h)),(model labels).rangeRestrict_surjective⟩

variable {U : Subgroup (Equiv.Perm (Fin 12))} (F : BinaryPairFrame U (Fin 6))
    (labels : Equiv.Perm (Fin 6)) (himage : F.top.range=(model labels).range)
def equiv : F.top.range ≃* Group :=
  (MulEquiv.subgroupCongr himage).trans (modelEquiv labels).symm

def topProjection : F.top.range →* Equiv.Perm (Fin 4) :=
  (MonoidHom.fst _ _).comp (equiv F labels himage).toMonoidHom

theorem topProjection_surjective : Function.Surjective (topProjection F labels himage) := by
  intro g
  exact ⟨(equiv F labels himage).symm (g,1),by simp [topProjection]⟩

include labels himage in
theorem top_card : Nat.card F.top.range=48 := by
  rw [Nat.card_congr (equiv F labels himage).toEquiv,Nat.card_prod,Nat.card_perm,
    Nat.card_perm,Nat.card_fin,Nat.card_fin]
  decide

theorem topProjection_kernel_card : Nat.card (topProjection F labels himage).ker=2 := by
  have hquot : Nat.card (F.top.range ⧸ (topProjection F labels himage).ker)=24 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (topProjection F labels himage) (topProjection_surjective F labels himage)).toEquiv]
    rw [Nat.card_perm,Nat.card_fin]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (topProjection F labels himage).ker
  rw [top_card F labels himage,hquot] at h
  omega
end SymmetricSubgroupAsymptotics.DoubleSymmetricFourSixImageConjugate
