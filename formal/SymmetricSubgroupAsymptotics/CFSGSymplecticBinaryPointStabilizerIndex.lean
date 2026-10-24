import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointExtension
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointDualOrbit
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorEvaluationSliceOrbitIndex
import SymmetricSubgroupAsymptotics.AbelianSemidirectStabilizerIndex
import Mathlib.LinearAlgebra.Quotient.Card

/-! One actual point-extension subgroup M supplies its additive kernel
J and projected subgroup L. The normalized detecting character lives in
an L-invariant affine half of Ann(J), so the factor2 follows from an
exact slice count rather than an unsupported prime multiplier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointStabilizerIndex
open CFSGSymplecticSerreMatrices CFSGSymplecticBinaryPointExtension
open CFSGSymplecticBinaryPointTailAction CFSGSymplecticBinaryPointDualOrbit
open InvariantAnnihilatorEvaluationSliceOrbitIndex
variable (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)

local instance finiteBinaryPointSemidirect {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (ρ : B →* MulAut A) : Finite (A ⋊[ρ] B) :=
  Finite.of_equiv (A × B) SemidirectProduct.equivProd.symm

omit [CharP K 2] in
private theorem nonzero_eq_one (hcard : Nat.card K = 2) (c : K) (hc : c ≠ 0) : c = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hs : c^2=c := by
    simpa only [← Nat.card_eq_fintype_card, hcard] using FiniteField.pow_card c
  have hp : c*(c-1)=0 := by linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hc)

/-- Field-cardinality two proves scalar closure of the actual additive
kernel; no field-linearity assumption is placed on M. -/
def kernelSubmodule (m : ℕ) (M : Subgroup (PointParabolic K hK m)) :
    Submodule K (CFSGSymplecticBinaryPointRadical.Coordinates K m) where
  carrier := {a | Multiplicative.ofAdd a ∈ M.comap SemidirectProduct.inl}
  zero_mem' := (M.comap SemidirectProduct.inl).one_mem
  add_mem' := fun ha hb => (M.comap SemidirectProduct.inl).mul_mem ha hb
  smul_mem' c a ha := by
    by_cases hc : c = 0
    · subst c
      simpa only [zero_smul] using (M.comap SemidirectProduct.inl).one_mem
    · have hc1 := nonzero_eq_one K hK c hc
      simpa only [hc1, one_smul] using ha

theorem quotient_card_eq_kernel_index (m : ℕ) (M : Subgroup (PointParabolic K hK m)) :
    Nat.card (CFSGSymplecticBinaryPointRadical.Coordinates K m ⧸ kernelSubmodule K hK m M) =
      (M.comap SemidirectProduct.inl).index := by
  let J := kernelSubmodule K hK m M
  let U := M.comap (SemidirectProduct.inl :
    Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m) →* PointParabolic K hK m)
  have hJ : Nat.card J = Nat.card U := rfl
  have hA : Nat.card (Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m)) =
      Nat.card (CFSGSymplecticBinaryPointRadical.Coordinates K m) :=
    Nat.card_congr Multiplicative.toAdd
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := J))
  calc
    _ = Nat.card (CFSGSymplecticBinaryPointRadical.Coordinates K m) :=
      (Submodule.card_eq_card_quotient_mul_card J).symm
    _ = Nat.card U * U.index := hA.symm.trans U.card_mul_index.symm
    _ = _ := by rw [hJ]

theorem semidirect_central_index_lower (s : ℕ) (hs : 0 < s)
    (M : Subgroup (PointParabolic K hK (s+1)))
    (hM : (SemidirectProduct.inl (Multiplicative.ofAdd (0,(1 : K))) :
      PointParabolic K hK (s+1)) ∉ M) :
    2^(s+1)*(2^(s+1)-1) ≤ M.index := by
  let J := kernelSubmodule K hK (s+1) M
  let L := M.map SemidirectProduct.rightHom
  let z : CFSGSymplecticBinaryPointRadical.Coordinates K (s+1) := (0,1)
  have hz : z ∉ J := hM
  obtain ⟨φ,hφ⟩ := exists_annihilator_eq_one_on J z hz
  have hJ : ∀ g ∈ L, ∀ a ∈ J, pointLinearHom K hK (s+1) g a ∈ J := by
    intro g hg a ha
    change Multiplicative.ofAdd a ∈ M.comap SemidirectProduct.inl at ha
    change tailAction K hK (s+1) g (Multiplicative.ofAdd a) ∈ M.comap SemidirectProduct.inl
    exact AbelianSemidirectStabilizerIndex.action_mem_kernel_of_projected
      (tailAction K hK (s+1)) M g hg (Multiplicative.ofAdd a) ha
  have hzfix : ∀ g ∈ L, pointLinearHom K hK (s+1) g z = z := by
    intro g _
    exact pointLinearHom_central K hK (s+1) g 1
  have ho := dual_orbit_mul_field_le_quotient_card_mul_index
    (pointLinearHom K hK (s+1)) L J hJ z hzfix φ hφ
  have hlower := actual_dual_orbit_card_lower K hK s hs φ.val hφ
  have hfac : Nat.card (CFSGSymplecticBinaryPointRadical.Coordinates K (s+1) ⧸ J) *
      L.index = M.index := by
    change Nat.card (CFSGSymplecticBinaryPointRadical.Coordinates K (s+1) ⧸
      kernelSubmodule K hK (s+1) M) * L.index = M.index
    rw [quotient_card_eq_kernel_index]
    exact (AbelianSemidirectStabilizerIndex.index_factor (tailAction K hK (s+1)) M).symm
  have hb : 2*((2^(s+1)-1)*2^s) ≤ M.index := by
    have hh := (Nat.mul_le_mul_left (Nat.card K) hlower).trans ho
    rw [hfac] at hh
    simpa only [hK] using hh
  calc
    _ = 2*((2^(s+1)-1)*2^s) := by rw [pow_succ]; ring
    _ ≤ _ := hb

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointStabilizerIndex
