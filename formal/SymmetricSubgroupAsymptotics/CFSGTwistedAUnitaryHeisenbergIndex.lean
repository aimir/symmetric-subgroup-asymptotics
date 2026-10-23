import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHeisenbergCommutator
import Mathlib.GroupTheory.Index

/-! Exact index factorization through the actual vector quotient, and
the prime-power divisibility forced by a proper central intersection.
The divisibility, rather than just an inequality, permits scaled Burnside
on the original permutation carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGKernelIndexFactor

theorem index_eq_kernel_relIndex_mul_map_index {G V : Type*}
    [Group G] [Group V] [Finite G] [Finite V]
    (f : G →* V) (hf : Function.Surjective f) (H : Subgroup G) :
    H.index = H.relIndex f.ker * (H.map f).index := by
  have h1 := Subgroup.relIndex_inf_mul_relIndex H f.ker ⊤
  have h2 := Subgroup.relIndex_inf_mul_relIndex f.ker H ⊤
  simp only [inf_top_eq, Subgroup.relIndex_top_right] at h1 h2
  have hk : f.ker.index = Nat.card V := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf]
    simp
  have hm : Nat.card (H.map f) * H.index = H.relIndex f.ker * Nat.card V := by
    rw [← Subgroup.relIndex_ker H f, ← hk, h2, h1, inf_comm]
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H.map f))
  calc
    Nat.card (H.map f) * H.index = H.relIndex f.ker * Nat.card V := hm
    _ = Nat.card (H.map f) * (H.relIndex f.ker * (H.map f).index) := by
      rw [← (H.map f).card_mul_index]
      ring

end SymmetricSubgroupAsymptotics.CFSGKernelIndexFactor

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates

theorem centralRadicalHom_range_eq_kernel (q : CFSG.PrimePower) (s : ℕ) :
    (centralRadicalHom q s).range = (fixedRadicalParameterHom q s).ker := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact centralRadicalHom_parameter q s c
  · intro hg
    obtain ⟨c, hc⟩ := exists_centralRadical_of_parameter_one q s g hg
    exact ⟨c, hc⟩

def radicalCentralPreimage (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) : Subgroup (Multiplicative (centralParameters q s)) :=
  H.comap (centralRadicalHom q s)

theorem radical_subgroup_index_factor (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) :
    H.index = (radicalCentralPreimage q s H).index *
      (H.map (fixedRadicalParameterHom q s)).index := by
  have hh := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    (fixedRadicalParameterHom q s) (fixedRadicalParameterHom_surjective q s) H
  have hc : (radicalCentralPreimage q s H).index =
      H.relIndex (fixedRadicalParameterHom q s).ker := by
    change (H.comap (centralRadicalHom q s)).index = _
    rw [Subgroup.index_comap, centralRadicalHom_range_eq_kernel]
  rw [hc]
  exact hh

theorem radicalVectorImage_card_le (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) (hH : ¬ (centralRadicalHom q s).range ≤ H) :
    Nat.card (radicalVectorImage q s H) ≤ q.order ^ (s + 1) := by
  let L := AddSubgroup.toZModSubmodule q.prime (radicalVectorImage q s H)
  have hk := radicalVectorImage_finrank_le q s H hH
  change Module.finrank (ZMod q.prime) L ≤ (s + 1) * q.exponent at hk
  have hc : Nat.card (radicalVectorImage q s H) =
      q.prime ^ Module.finrank (ZMod q.prime) L := by
    change Nat.card L = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod q.prime), Nat.card_zmod]
  rw [hc]
  calc
    _ ≤ q.prime ^ ((s + 1) * q.exponent) := Nat.pow_le_pow_right q.prime_isPrime.pos hk
    _ = q.order ^ (s + 1) := by
      change q.prime ^ ((s + 1) * q.exponent) = (q.prime ^ q.exponent) ^ (s + 1)
      rw [← pow_mul, Nat.mul_comm (s + 1)]

theorem radicalVectorImage_index_dvd (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) (hH : ¬ (centralRadicalHom q s).range ≤ H) :
    q.order ^ (s + 1) ∣ (H.map (fixedRadicalParameterHom q s)).index := by
  let L := radicalVectorImage q s H
  let Lp := AddSubgroup.toZModSubmodule q.prime L
  let k := Module.finrank (ZMod q.prime) Lp
  let d := (s + 1) * q.exponent
  have hk : k ≤ d := radicalVectorImage_finrank_le q s H hH
  have hcardL : Nat.card L = q.prime ^ k := by
    change Nat.card Lp = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod q.prime), Nat.card_zmod]
  have hcardV : Nat.card (Fin (s + 1) → q.Extension 2) = q.prime ^ (2 * d) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q.prime), Nat.card_zmod,
      primeVector_finrank]
  have hindex : L.index = q.prime ^ (2 * d - k) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos q.prime_isPrime.pos k)
    calc
      q.prime ^ k * L.index = Nat.card (Fin (s + 1) → q.Extension 2) := by
        rw [← hcardL, L.card_mul_index]
      _ = q.prime ^ (2 * d) := hcardV
      _ = q.prime ^ k * q.prime ^ (2 * d - k) := by
        rw [← pow_add]
        congr 1
        omega
  have hqd : q.order ^ (s + 1) = q.prime ^ d := by
    change (q.prime ^ q.exponent) ^ (s + 1) = q.prime ^ ((s + 1) * q.exponent)
    rw [← pow_mul, Nat.mul_comm q.exponent]
  change q.order ^ (s + 1) ∣ L.index
  rw [hindex, hqd]
  refine ⟨q.prime ^ (2 * d - k - d), ?_⟩
  rw [← pow_add]
  congr 1
  omega

theorem radical_subgroup_index_central_divisibility (q : CFSG.PrimePower) (s : ℕ)
    (H : Subgroup (fixedRadical q s)) (hH : ¬ (centralRadicalHom q s).range ≤ H) :
    ∃ m : ℕ, H.index = (radicalCentralPreimage q s H).index *
      (q.order ^ (s + 1) * m) := by
  obtain ⟨m, hm⟩ := radicalVectorImage_index_dvd q s H hH
  exact ⟨m, (radical_subgroup_index_factor q s H).trans (congrArg
    (fun n : ℕ => (radicalCentralPreimage q s H).index * n) hm)⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
