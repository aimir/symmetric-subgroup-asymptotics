import SymmetricSubgroupAsymptotics.ActualNormalLayerOrbitIndex
import SymmetricSubgroupAsymptotics.BinaryQuadraticLiftIsotropicDualOrbit
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorEvaluationSliceOrbitIndex
import Mathlib.LinearAlgebra.Quotient.Card

/-! A normalized central character for the SAME intersection with an
actual normal subgroup. Binary scalar closure is proved, not assumed.
Only one isotropic family of transvections is required; no split
extension or full symplectic image is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryNormalCentralEvaluationIndex
open BinaryQuadraticLiftAction BinaryQuadraticRefinementTransvections
open InvariantAnnihilatorEvaluationSliceOrbitIndex
variable {K I P : Type} [Field K] [Finite K] [CharP K 2]
    [Fintype I] [Group P] [Finite P]
private abbrev A := Coordinates (K := K) (I := I)

omit [CharP K 2] in
private theorem nonzero_eq_one (hK : Nat.card K=2) (a : K) (ha : a≠0) : a=1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hs : a^2=a := by
    simpa only [←Nat.card_eq_fintype_card,hK] using FiniteField.pow_card a
  have hz : a*(a-1)=0 := by rw [mul_sub,mul_one,←pow_two,hs,sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)

def centralSubmodule (hK : Nat.card K=2) (N M : Subgroup P)
    (ι : Multiplicative (A (K := K) (I := I)) →* N) :
    Submodule K (A (K := K) (I := I)) where
  carrier := {a | ι (Multiplicative.ofAdd a) ∈ M.comap N.subtype}
  zero_mem' := by change ι 1 ∈ M.comap N.subtype; rw [map_one]; exact Subgroup.one_mem _
  add_mem' {a b} ha hb := by
    change ι (Multiplicative.ofAdd a * Multiplicative.ofAdd b) ∈ M.comap N.subtype
    rw [map_mul]
    exact (M.comap N.subtype).mul_mem ha hb
  smul_mem' a x hx := by
    by_cases ha : a=0
    · subst a
      rw [zero_smul]
      change ι 1 ∈ M.comap N.subtype
      rw [map_one]
      exact Subgroup.one_mem _
    · simpa only [nonzero_eq_one hK a ha,one_smul] using hx

omit [Fintype I] [Finite P] in
theorem centralSubmodule_card (hK : Nat.card K=2) (N M : Subgroup P)
    (ι : Multiplicative (A (K := K) (I := I)) →* N) :
    Nat.card (centralSubmodule hK N M ι) = Nat.card ((M.comap N.subtype).comap ι) := rfl

theorem normalized_central_orbit_capacity (hK : Nat.card K=2)
    (N M : Subgroup P) [N.Normal]
    (ι : Multiplicative (A (K := K) (I := I)) →* N) (hι : Function.Injective ι)
    (hcentral : ∀ z, ι z ∈ Subgroup.center N)
    (ρ : P →* Vector (K := K) (I := I) ≃ₗ[K] Vector (K := K) (I := I))
    (hB : ∀ g v w, polar (ρ g v) (ρ g w)=polar v w)
    (hequiv : ∀ p a, ι (Multiplicative.ofAdd (liftHom hK ρ hB p a)) =
      MulAut.conjNormal p (ι (Multiplicative.ofAdd a)))
    (htransY : ∀ v : I → K, ∃ g : P, ∀ x, ρ g x=transvectionMap (0,v) x)
    (hM : ι (Multiplicative.ofAdd ((0,1) : A (K := K) (I := I))) ∉ M.comap N.subtype)
    (hI : 0<Fintype.card I) :
    Nat.card K * Nat.card K^(Fintype.card I-1) *
        Nat.card ((M.comap N.subtype).comap ι) ≤
      Nat.card (A (K := K) (I := I)) * (M ⊔ N).index := by
  let J := centralSubmodule hK N M ι
  let τ := liftHom hK ρ hB
  have hN (n : P) (hn : n ∈ N) (a : A (K := K) (I := I)) : τ n a=a := by
    apply Multiplicative.ofAdd.injective
    apply hι
    rw [hequiv]
    apply Subtype.ext
    change n * (ι (Multiplicative.ofAdd a) : P) * n⁻¹ = _
    have hc := Subgroup.mem_center_iff.mp (hcentral (Multiplicative.ofAdd a)) (⟨n,hn⟩ : N)
    have hc' : n * (ι (Multiplicative.ofAdd a) : P) =
        (ι (Multiplicative.ofAdd a) : P) * n :=
      congrArg (fun t : N => (t : P)) hc
    rw [hc',mul_assoc,mul_inv_cancel,mul_one]
  have hJ : ∀ p ∈ M ⊔ N, ∀ a ∈ J, τ p a ∈ J := by
    intro p hp a ha
    obtain ⟨m,hm,n,hn,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hp
    change τ (m*n) a ∈ J
    rw [map_mul]
    change τ m (τ n a) ∈ J
    rw [hN n hn]
    change (ι (Multiplicative.ofAdd (τ m a)) : P) ∈ M
    rw [hequiv]
    change m * (ι (Multiplicative.ofAdd a) : P) * m⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hm ha) (M.inv_mem hm)
  obtain ⟨φ,hφ⟩ := exists_annihilator_eq_one_on J (0,1) hM
  have ho := dual_orbit_mul_field_le_quotient_card_mul_index τ (M ⊔ N) J hJ
    (0,1) (fun g _ => liftHom_central hK ρ hB g 1) φ hφ
  have hl := BinaryQuadraticLiftIsotropicDualOrbit.dual_orbit_card_lower
    hK ρ hB htransY φ.val hφ hI
  have hh := Nat.mul_le_mul_right (Nat.card J) ((Nat.mul_le_mul_left (Nat.card K) hl).trans ho)
  rw [centralSubmodule_card hK N M ι] at hh
  calc
    _ ≤ (Nat.card (A (K := K) (I := I) ⧸ J) * (M ⊔ N).index) * Nat.card J := hh
    _ = (Nat.card J * Nat.card (A (K := K) (I := I) ⧸ J)) * (M ⊔ N).index := by ring
    _ = _ := by rw [←Submodule.card_eq_card_quotient_mul_card J]

end SymmetricSubgroupAsymptotics.BinaryNormalCentralEvaluationIndex
