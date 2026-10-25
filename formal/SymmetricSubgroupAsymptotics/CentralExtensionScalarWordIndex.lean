import SymmetricSubgroupAsymptotics.ScalarCentrePrimeFieldAction
import SymmetricSubgroupAsymptotics.ScalarWordDualAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.ActualNormalLayerOrbitIndex
import SymmetricSubgroupAsymptotics.CentralLayerOrbitCapacityNumerics
import Mathlib.LinearAlgebra.Quotient.Card

/-! Scalar words on the full centre and nondegenerate scalar commutators
pay one coupled index bound. The central intersection is arbitrary over
the prime field and belongs to the same radical intersection and join. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralExtensionScalarWordIndex
open CentralExtensionScalarPairingIndex CentralExtensionScalarPairingCentre
open ScalarCentrePrimeFieldAction InvariantAnnihilatorOrbitIndex
variable {P K V : Type*} [Group P] [Finite P] [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [Finite V]

theorem index_le_of_scalar_words (N : Subgroup P) [N.Normal]
    (D : Data (F := K) (V := V) (N := N))
    (p m : ℕ) [Fact p.Prime] [CharP K p]
    (hdim : Module.finrank K V = 2*m)
    (χ : P →* MulAut (Multiplicative K))
    (hequiv : ∀ g a, D.central (χ g a) = MulAut.conjNormal g (D.central a))
    (hscalar : ∀ a : Kˣ, ∃ g : P, ∀ b : K,
      χ g (Multiplicative.ofAdd b) = Multiplicative.ofAdd ((a : K)*b))
    (M : Subgroup P) (hM : (D.central (Multiplicative.ofAdd (1 : K))).val ∉ M) :
    Nat.card K^m*(Nat.card K-1) ≤ M.index := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  let J : Subgroup N := M.comap N.subtype
  let C : Subgroup (Multiplicative K) := J.comap D.central
  let W : Subgroup (Multiplicative V) := J.map D.projection
  let L : Subgroup P := M ⊔ N
  let A : Submodule (ZMod p) K := AddSubgroup.toZModSubmodule p C.toAddSubgroup'
  let ρ : P →* K ≃ₗ[ZMod p] K := (linearAction p).comp χ
  have hJ : ¬D.central.range ≤ J := by
    intro hh
    exact hM (hh ⟨Multiplicative.ofAdd (1 : K),rfl⟩)
  have hw : Nat.card W ≤ Nat.card K^m := D.vectorImage_card_le p m hdim J hJ
  have hC : ∀ g ∈ L, ∀ a ∈ C, χ g a ∈ C :=
    ActualNormalLayerOrbitIndex.central_layer_invariant N M D.central D.central_injective
      (fun a => central_range_le_center D ⟨a,rfl⟩) χ hequiv
  have hA : ∀ g ∈ L, ∀ x ∈ A, ρ g x ∈ A := by
    intro g hg x hx
    exact hC g hg (Multiplicative.ofAdd x) hx
  have hAscalar : ∀ a : Kˣ, ∃ g : P, ∀ x : K, ρ g x = (a : K)*x := by
    intro a
    obtain ⟨g,hg⟩ := hscalar a
    exact ⟨g,fun x => congrArg Multiplicative.toAdd (hg x)⟩
  have h1 : (1 : K) ∉ A := hM
  obtain ⟨f,hf⟩ := exists_annihilator_nonzero_on A (1 : K) h1
  have hf0 : f.val ≠ 0 := by
    intro hh
    exact hf (by rw [hh]; rfl)
  have ho := ScalarWordDualAnnihilatorOrbitIndex.quotient_card_mul_index_ge
    ρ hAscalar L A hA f hf0
  have hAC : Nat.card A = Nat.card C := Nat.card_congr
    ({ toFun := fun x => ⟨Multiplicative.ofAdd x.val,x.property⟩
       invFun := fun x => ⟨x.val.toAdd,x.property⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : A ≃ C)
  have hcard : Nat.card K = Nat.card (K ⧸ A)*Nat.card C := by
    calc
      Nat.card K = Nat.card A*Nat.card (K ⧸ A) := Submodule.card_eq_card_quotient_mul_card A
      _ = Nat.card (K ⧸ A)*Nat.card C := by rw [hAC]; exact Nat.mul_comm _ _
  have hc : (Nat.card K-1)*Nat.card C ≤ Nat.card K*L.index := by
    calc
      _ ≤ (Nat.card (K ⧸ A)*L.index)*Nat.card C := Nat.mul_le_mul_right _ ho
      _ = Nat.card K*L.index := by rw [hcard]; ring
  have he := ActualNormalLayerOrbitIndex.index_mul_layer_cards N M D.projection
    D.projection_surjective D.central D.central_range
  change M.index*Nat.card C*Nat.card W = Nat.card K*Nat.card (Multiplicative V)*L.index at he
  have hV : Nat.card (Multiplicative V) = Nat.card K^(2*m) := by
    change Nat.card V = _
    rw [Module.natCard_eq_pow_finrank (K := K),hdim]
  rw [hV] at he
  have hn := CentralLayerOrbitCapacityNumerics.normalized_orbit_capacity 1
    (Nat.card K-1) (Nat.card K) (Nat.card K^(2*m)) M.index
    (Nat.card C) (Nat.card W) L.index (Nat.card K^m)
    (Nat.card_pos (α := C)) hw (by simpa only [one_mul] using hc) he
  apply Nat.le_of_mul_le_mul_right _ (pow_pos (Nat.card_pos (α := K)) m)
  calc
    (Nat.card K^m*(Nat.card K-1))*Nat.card K^m =
        (Nat.card K-1)*Nat.card K^(2*m) := by rw [two_mul,pow_add]; ring
    _ ≤ M.index*Nat.card K^m := by simpa only [one_mul] using hn

end SymmetricSubgroupAsymptotics.CentralExtensionScalarWordIndex
