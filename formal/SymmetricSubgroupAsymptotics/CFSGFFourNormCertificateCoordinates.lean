import SymmetricSubgroupAsymptotics.CFSGFFourE6NormPairRepresentatives
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Card

/-! The selected 26 labels used by the one-vector certificate are
identified with the actual norm-basis labels. Only the existing24 root
representatives are listed; no matrix or group elements are enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateCoordinates
open CFSGFFourE6NormPairRepresentatives

def rootData : Fin 24 → Fin 6 → ℤ := ![
  ![-1,-1,-2,-2,-1,-1], ![-1,-1,-2,-2,-1,0],
  ![-1,-1,-1,-2,-1,0], ![-1,-1,-1,-1,-1,0],
  ![-1,-1,-1,-1,0,0], ![-1,0,-1,-1,-1,0],
  ![-1,0,-1,-1,0,0], ![-1,0,-1,0,0,0],
  ![-1,0,0,0,0,0], ![0,-1,-1,-1,0,0],
  ![0,0,-1,-1,0,0], ![0,0,-1,0,0,0],
  ![0,0,0,0,0,1], ![0,0,0,0,1,0],
  ![0,0,0,0,1,1], ![0,0,0,1,1,0],
  ![0,0,0,1,1,1], ![0,0,1,1,1,1],
  ![0,1,0,1,1,0], ![0,1,0,1,1,1],
  ![0,1,1,1,1,1], ![0,1,1,2,1,1],
  ![0,1,1,2,2,1], ![1,1,1,2,2,1]]

theorem rootData_mem : ∀i : Fin 24, rootData i ∈ rootRepresentatives := by decide +kernel

private theorem rootData_injective_certificate : ∀i j : Fin 24,
    rootData i = rootData j → i = j := by decide +kernel

def rootIndex (i : Fin 24) : rootRepresentatives := ⟨rootData i,rootData_mem i⟩

theorem rootIndex_injective : Function.Injective rootIndex := by
  intro i j h
  exact rootData_injective_certificate i j (congrArg Subtype.val h)

def rootEquiv : Fin 24 ≃ rootRepresentatives :=
  Equiv.ofBijective rootIndex ((Nat.bijective_iff_injective_and_card rootIndex).mpr
    ⟨rootIndex_injective,by
      simp only [Nat.card_eq_fintype_card,Fintype.card_fin,Fintype.card_coe,rootRepresentatives_card]⟩)

def coordinateEquiv : Fin 26 ≃ PairIndex :=
  (finSumFinEquiv : Fin 2 ⊕ Fin 24 ≃ Fin 26).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin 2)) rootEquiv)

theorem coordinate_left (i : Fin 2) :
    coordinateEquiv (Fin.castAdd 24 i) = Sum.inl i := by
  exact congrArg (Equiv.sumCongr (Equiv.refl (Fin 2)) rootEquiv)
    ((finSumFinEquiv : Fin 2 ⊕ Fin 24 ≃ Fin 26).symm_apply_apply (Sum.inl i))

theorem coordinate_right (i : Fin 24) :
    coordinateEquiv (Fin.natAdd 2 i) = Sum.inr (rootIndex i) := by
  exact congrArg (Equiv.sumCongr (Equiv.refl (Fin 2)) rootEquiv)
    ((finSumFinEquiv : Fin 2 ⊕ Fin 24 ≃ Fin 26).symm_apply_apply (Sum.inr i))

end SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateCoordinates
