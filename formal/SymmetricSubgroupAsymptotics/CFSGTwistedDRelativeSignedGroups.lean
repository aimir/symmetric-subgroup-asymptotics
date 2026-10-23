import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPositiveSimpleUnipotent
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSwapTriangular

/-! The literal positive and negative relative-root closures are actual
p-groups. The negative closure embeds in the SAME upper-unitriangular
matrix group after the explicit all-pairs conjugation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeSignedGroups
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDSingularPrefix CFSGTwistedA2FixedField
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDIndexUnipotent CFSGOrthogonalDPositiveSimpleUnipotent
open CFSGOrthogonalDAllPairSwap CFSGOrthogonalDSwapTriangular

def signedGenerators (n : ℕ) (q : CFSG.PrimePower) (neg : Bool) :
    Set ((Mat (q.Extension 2) (n + 2))ˣ) :=
  {g | (∃ (i : Fin n) (a : fixedField q),
      g = rootTransvection (q.Extension 2) (n + 2) neg (chainNode n i) (a : q.Extension 2)) ∨
    ∃ a : q.Extension 2, g = pairedRoot n q neg a}

def signedRootGroup (n : ℕ) (q : CFSG.PrimePower) (neg : Bool) :
    Subgroup ((Mat (q.Extension 2) (n + 2))ˣ) := Subgroup.closure (signedGenerators n q neg)

theorem positive_sup_negative (n : ℕ) (q : CFSG.PrimePower) :
    signedRootGroup n q false ⊔ signedRootGroup n q true = relativeRootGroup n q := by
  rw [signedRootGroup, signedRootGroup, ← Subgroup.closure_union]
  congr 1
  ext g
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨i, a, h⟩ | ⟨a, h⟩
      · exact Or.inl ⟨false, i, a, h⟩
      · exact Or.inr ⟨false, a, h⟩
    · rcases h with ⟨i, a, h⟩ | ⟨a, h⟩
      · exact Or.inl ⟨true, i, a, h⟩
      · exact Or.inr ⟨true, a, h⟩
  · intro h
    rcases h with ⟨neg, i, a, h⟩ | ⟨neg, a, h⟩
    · cases neg
      · exact Or.inl (Or.inl ⟨i, a, h⟩)
      · exact Or.inr (Or.inl ⟨i, a, h⟩)
    · cases neg
      · exact Or.inl (Or.inr ⟨a, h⟩)
      · exact Or.inr (Or.inr ⟨a, h⟩)

theorem positive_le_upper_units (n : ℕ) (q : CFSG.PrimePower) :
    signedRootGroup n q false ≤ CFSGMatrixFlagSubgroups.unipotentUnits
      (K := q.Extension 2) (flagEquiv (n + 2)) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨i, a, rfl⟩ | ⟨a, rfl⟩
  · exact positive_mem_unipotent (q.Extension 2) (n + 2) _ _
  · exact (CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (n + 2))).mul_mem
      (positive_mem_unipotent (q.Extension 2) (n + 2) _ _)
      (positive_mem_unipotent (q.Extension 2) (n + 2) _ _)

theorem negative_root_transpose_val (K : Type) [Field K] (r : ℕ) (i : Fin r) (a : K) :
    (rootTransvection K r true i a : Mat K r).transpose =
      (rootTransvection K r false i a : Mat K r) := by
  change (1 + a • negative K r i).transpose = 1 + a • positive K r i
  simp only [negative, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_transpose]

theorem negative_root_conjugate_upper (K : Type) [Field K] (r : ℕ) (i : Fin r) (a : K) :
    (MulAut.conj (pairSwap K r)) (rootTransvection K r true i a) ∈
      CFSGMatrixFlagSubgroups.unipotentUnits (K := K) (flagEquiv r) := by
  have hp := positive_mem_unipotent K r i a
  have ht : (rootTransvection K r true i a : Mat K r).transpose.BlockTriangular (flagEquiv r) := by
    rw [negative_root_transpose_val]
    exact hp.1
  refine ⟨pairSwap_conjugate_triangular K r _ ht, fun x => ?_⟩
  change ((pairSwap K r : Mat K r) * (rootTransvection K r true i a : Mat K r) *
    (pairSwap K r : Mat K r)) x x = 1
  rw [pairSwap_conjugation_entry]
  have h := congrArg (fun M : Mat K r => M (Sum.swap x) (Sum.swap x))
    (negative_root_transpose_val K r i a)
  exact h.trans (hp.2 (Sum.swap x))

theorem negative_conjugate_le_upper_units (n : ℕ) (q : CFSG.PrimePower) :
    signedRootGroup n q true ≤
      (CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (n + 2))).comap
        (MulAut.conj (pairSwap (q.Extension 2) (n + 2))).toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨i, a, rfl⟩ | ⟨a, rfl⟩
  · exact negative_root_conjugate_upper (q.Extension 2) (n + 2) _ _
  · change (MulAut.conj (pairSwap (q.Extension 2) (n + 2)))
      (rootTransvection (q.Extension 2) (n + 2) true (pen n) a *
        rootTransvection (q.Extension 2) (n + 2) true (last n)
          (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 a)) ∈
        CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (n + 2))
    rw [map_mul]
    exact (CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (n + 2))).mul_mem
      (negative_root_conjugate_upper (q.Extension 2) (n + 2) _ _)
      (negative_root_conjugate_upper (q.Extension 2) (n + 2) _ _)

theorem signedRootGroup_isPGroup (n : ℕ) (q : CFSG.PrimePower) (neg : Bool) :
    IsPGroup q.prime (signedRootGroup n q neg) := by
  have hU := CFSGMatrixFlagSubgroups.unipotentUnits_isPGroup
    (K := q.Extension 2) (flagEquiv (n + 2)) q.prime
  cases neg with
  | false =>
    exact hU.of_injective (Subgroup.inclusion (positive_le_upper_units n q))
      (fun x y h => Subtype.ext (congrArg
        (fun u : CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (n + 2)) => u.val) h))
  | true =>
    let f := (MulAut.conj (pairSwap (q.Extension 2) (n + 2))).toMonoidHom
    have hP := hU.comap_of_injective f (MulAut.conj (pairSwap (q.Extension 2) (n + 2))).injective
    exact hP.of_injective (Subgroup.inclusion (negative_conjugate_le_upper_units n q))
      (fun x y h => Subtype.ext (congrArg
        (fun u : (CFSGMatrixFlagSubgroups.unipotentUnits (K := q.Extension 2) (flagEquiv (n + 2))).comap f => u.val) h))

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeSignedGroups
