import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.SetTheory.Cardinal.Finite

/-! Cardinality of the genuine rank-one torus envelope.  The parameter
maps are proved multiplicative from their actual diagonal matrices, and
their commuting product surjects onto the subgroup they generate.  This
does not identify the full diagonal normalizer with this torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckDiagonalTorus CFSGNormTwoGeckBorelEnvelope
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (K : Type) [Field K]

theorem parameterTorus_mul (i : Fin r) (t u : Kˣ) :
    parameterTorus A hs hp b s K i (t*u)=
      parameterTorus A hs hp b s K i t*parameterTorus A hs hp b s K i u := by
  apply Units.ext
  rw [Units.val_mul,torus_diagonal,torus_diagonal,torus_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_zpow (t:K) (u:K) _

theorem parameterTorus_one (i : Fin r) :
    parameterTorus A hs hp b s K i 1=1 := by
  apply Units.ext
  rw [torus_diagonal]
  simp only [Units.val_one,one_zpow]
  exact Matrix.diagonal_one

def simpleTorusHom (i : Fin r) : Kˣ→*
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ where
  toFun:=parameterTorus A hs hp b s K i
  map_one':=parameterTorus_one A hs hp b s K i
  map_mul':=parameterTorus_mul A hs hp b s K i

theorem parameterTorus_commute (i j : Fin r) (t u : Kˣ) :
    Commute (parameterTorus A hs hp b s K i t) (parameterTorus A hs hp b s K j u) := by
  apply Units.ext
  simp only [Units.val_mul,torus_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

def allToriHom : (Fin r→Kˣ)→*
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  MonoidHom.noncommPiCoprod (simpleTorusHom A hs hp b s K)
    (fun i j _ t u=>parameterTorus_commute A hs hp b s K i j t u)

theorem allToriHom_range : (allToriHom A hs hp b s K).range=torusGroup A hs hp b s K := by
  rw [allToriHom,MonoidHom.noncommPiCoprod_range]
  apply le_antisymm
  · apply iSup_le
    intro i x hx
    obtain ⟨t,rfl⟩:=hx
    exact Subgroup.subset_closure ⟨(i,t),rfl⟩
  · apply (Subgroup.closure_le _).2
    rintro x ⟨⟨i,t⟩,rfl⟩
    exact (le_iSup (fun j=>(simpleTorusHom A hs hp b s K j).range) i) ⟨t,rfl⟩

theorem torus_card_le_units_pow [Finite K] :
    Nat.card (torusGroup A hs hp b s K)≤Nat.card Kˣ^r := by
  have h:=Nat.card_le_card_of_surjective (allToriHom A hs hp b s K).rangeRestrict
    (allToriHom A hs hp b s K).rangeRestrict_surjective
  rw [allToriHom_range] at h
  simpa only [Nat.card_fun,Nat.card_fin] using h

theorem torus_card_le_field_pow [Finite K] :
    Nat.card (torusGroup A hs hp b s K)≤Nat.card K^r := by
  apply (torus_card_le_units_pow A hs hp b s K).trans
  exact Nat.pow_le_pow_left (Nat.card_le_card_of_injective Units.val Units.val_injective) r

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusCardinality
