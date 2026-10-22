import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexRootComponents
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixPerpendicular
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPrefixDimension
import SymmetricSubgroupAsymptotics.CFSGQuadraticFlagConjugator

/-! In the actual elementary D4 group, preservation of the first three
positive prefixes forces triangularity. Genuine quadratic component
parity excludes the last hyperbolic-pair interchange, in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourPartialFlagUpper
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexPositiveSpace CFSGOrthogonalDIndexRootComponents
open CFSGOrthogonalDIndexPrefixPerpendicular CFSGOrthogonalDIndexPolarForm
open CFSGOrthogonalDIndexPrefixDimension CFSGMatrixFlagNormalizer
variable (K : Type) [Field K]

theorem fourthPrefix_eq_positive :
    flagPrefix (K := K) (flagEquiv 4) 4 = positiveSpace K 4 := by
  ext v
  constructor
  · intro hv i
    exact hv (Sum.inr i) (by change 4 ≤ 4 + (Fin.rev i).val; omega)
  · intro hv x hx
    cases x with
    | inl i => change 4 ≤ i.val at hx; omega
    | inr i => exact hv i

theorem positive_map_eq (A : elementaryRootGroup K 4)
    (hmap : (flagPrefix (K := K) (flagEquiv 4) 3).map
      (naturalLinearHom K 4 A).toLinearMap = flagPrefix (K := K) (flagEquiv 4) 3) :
    (positiveSpace K 4).map (naturalLinearHom K 4 A).toLinearMap = positiveSpace K 4 := by
  let P := positiveSpace K 4
  let L := naturalLinearHom K 4 A
  let F := flagPrefix (K := K) (flagEquiv 4) 3
  let I : Submodule K (Index 4 → K) := P ⊓ P.map L.toLinearMap
  have hmapF : F.map L.toLinearMap = F := hmap
  have hFP : F ≤ P := by
    intro v hv i
    exact hv (Sum.inr i) (by change 3 ≤ 4 + (Fin.rev i).val; omega)
  have hFI : F ≤ P ⊓ P.map L.toLinearMap := by
    refine le_inf hFP ?_
    rw [← hmapF]
    exact Submodule.map_mono hFP
  have hlow : 3 ≤ Module.finrank K I := by
    have h := Submodule.finrank_mono hFI
    have hf : Module.finrank K F = 3 := flagPrefix_finrank K (flagEquiv 4) 3 (by omega)
    rwa [hf] at h
  have hupp : Module.finrank K I ≤ 4 := by
    have h := Submodule.finrank_mono (show P ⊓ P.map L.toLinearMap ≤ P from inf_le_left)
    have hp : Module.finrank K P = 4 := positiveSpace_finrank K 4
    rwa [hp] at h
  have he := elementary_even_distance K 0 A
  change Even (4 - Module.finrank K I) at he
  obtain ⟨n, hn⟩ := he
  have hd : Module.finrank K I = 4 := by omega
  have hIP : P ⊓ P.map L.toLinearMap = P :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (hd.trans (positiveSpace_finrank K 4).symm)
  apply Submodule.eq_of_le_of_finrank_eq
  · have hle : P ≤ P.map L.toLinearMap := calc
      P = I := hIP.symm
      _ ≤ P.map L.toLinearMap := (inf_le_right : P ⊓ P.map L.toLinearMap ≤ P.map L.toLinearMap)
    have heq : P = P.map L.toLinearMap := Submodule.eq_of_le_of_finrank_eq hle
      (L.finrank_map_eq P).symm
    exact heq.ge
  · exact L.finrank_map_eq P

theorem triangular (A : elementaryRootGroup K 4)
    (hpres : ∀ k, k ≤ 3 → ∀ v ∈ flagPrefix (K := K) (flagEquiv 4) k,
      (A.val : Mat K 4) *ᵥ v ∈ flagPrefix (K := K) (flagEquiv 4) k) :
    (A.val : Mat K 4).BlockTriangular (flagEquiv 4) := by
  let L := naturalLinearHom K 4 A
  have hmap : ∀ k, k ≤ 4 → (flagPrefix (K := K) (flagEquiv 4) k).map L.toLinearMap =
      flagPrefix (K := K) (flagEquiv 4) k := by
    intro k hk
    by_cases hsmall : k ≤ 3
    · exact CFSGQuadraticFlagConjugator.map_eq_of_preserves L _ (hpres k hsmall)
    · have hk4 : k = 4 := by omega
      subst k
      rw [fourthPrefix_eq_positive]
      exact positive_map_eq K A
        (CFSGQuadraticFlagConjugator.map_eq_of_preserves L _ (hpres 3 (by omega)))
  have hp (k : ℕ) (hk : k ≤ 4) (v : Index 4 → K)
      (hv : v ∈ flagPrefix (K := K) (flagEquiv 4) k) :
      L v ∈ flagPrefix (K := K) (flagEquiv 4) k := by
    rw [← hmap k hk]
    exact ⟨v, hv, rfl⟩
  have hi (k : ℕ) (hk : k ≤ 4) (v : Index 4 → K)
      (hv : v ∈ flagPrefix (K := K) (flagEquiv 4) k) :
      L.symm v ∈ flagPrefix (K := K) (flagEquiv 4) k := by
    rw [← hmap k hk] at hv
    rcases hv with ⟨w, hw, he⟩
    change L w = v at he
    rw [← he, L.symm_apply_apply]
    exact hw
  intro x y hxy
  cases y with
  | inl j =>
    have hv : (Pi.single (Sum.inl j) (1 : K) : Index 4 → K) ∈
        flagPrefix (K := K) (flagEquiv 4) (j.val + 1) := by
      intro z hz
      apply Pi.single_eq_of_ne
      intro he; subst z
      change j.val + 1 ≤ j.val at hz
      omega
    have h := hp (j.val + 1) (by omega) _ hv x (by
      change j.val < (flagEquiv 4 x).val at hxy
      omega)
    change ((A.val : Mat K 4) *ᵥ Pi.single (Sum.inl j) 1) x = 0 at h
    rwa [Matrix.mulVec_single_one] at h
  | inr j =>
    cases x with
    | inl i => exact False.elim ((not_lt_of_gt (flag_pos_lt_neg 4 i j)) hxy)
    | inr i =>
      have hij : i < j := by
        apply Fin.rev_lt_rev.mp
        change 4 + (Fin.rev j).val < 4 + (Fin.rev i).val at hxy
        change (Fin.rev j).val < (Fin.rev i).val
        omega
      have hv : (Pi.single (Sum.inl i) (1 : K) : Index 4 → K) ∈
          flagPrefix (K := K) (flagEquiv 4) (i.val + 1) := by
        intro z hz
        apply Pi.single_eq_of_ne
        intro he; subst z
        change i.val + 1 ≤ i.val at hz
        omega
      have hw : (Pi.single (Sum.inr j) (1 : K) : Index 4 → K) ∈
          positivePerpendicular K 4 (i.val + 1) := by
        intro l hl
        have hlj : l ≠ j := by intro he; subst l; omega
        simp [hlj]
      have hz := prefix_polar_zero K 4 (i.val + 1) (by omega) _ _
        (hi (i.val + 1) (by omega) _ hv) hw
      have he := elementary_preserves_polar K 0 A (L.symm (Pi.single (Sum.inl i) 1))
        (Pi.single (Sum.inr j) 1)
      change polar K (L (L.symm (Pi.single (Sum.inl i) 1)))
        (L (Pi.single (Sum.inr j) 1)) = _ at he
      rw [L.apply_symm_apply, polar_positive_basis] at he
      have he0 := he.trans hz
      change ((A.val : Mat K 4) *ᵥ Pi.single (Sum.inr j) 1) (Sum.inr i) = 0 at he0
      rwa [Matrix.mulVec_single_one] at he0

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourPartialFlagUpper
