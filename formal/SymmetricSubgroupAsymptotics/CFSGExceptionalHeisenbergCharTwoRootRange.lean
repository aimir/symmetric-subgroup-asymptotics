import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootRange
import Mathlib.Algebra.CharP.Two

/-! In characteristic two the normalized Y parameters coincide with the
literal selected-root parameters. Consequently the actual chart range is
the join indexed by the displayed X/Y/central root labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergCharTwoRootRange
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalHeisenbergRootPilot
open CFSGExceptionalHeisenbergRootRelations CFSGExceptionalHeisenbergProduct
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGExceptionalHeisenbergRootRange
variable {r m : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i,A i i=2)
  (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
  (ho : ∀ i j,i≠j→A i j≤0)
  [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
  (C : RootConfig A m)
private abbrev Label (m : ℕ) := Fin m ⊕ (Fin m ⊕ Unit)

def rootFamily : Label m → Roots A
  | .inl i => (C.xRoot i).val
  | .inr (.inl i) => (C.yRoot i).val
  | .inr (.inr _) => C.zRoot.val

theorem yNegative_eq_selectedRootHom (K : Type) [CommRing K] [CharP K 2] (i : Fin m) :
    yNegative A hd hs hp ho C K i = selectedRootHom A hd hs hp ho K (C.yRoot i).val := by
  apply MonoidHom.ext
  intro t
  change selectedRootElement A hd hs hp ho K (C.yRoot i).val
      (((pairSign A hd hs hp ho C i : ℤ) : K)*(-t.toAdd)) =
    selectedRootElement A hd hs hp ho K (C.yRoot i).val t.toAdd
  have hsign : ((pairSign A hd hs hp ho C i : ℤ) : K)=1 := by
    rcases pairSign_unit A hd hs hp ho C i with h | h <;>
      rw [h] <;> simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq]
  rw [hsign,CharTwo.neg_eq,one_mul]

theorem rawHom_range_eq_selected_join (K : Type) [CommRing K] [CharP K 2] :
    (rawHom A hd hs hp ho C K).range =
      ⨆ b : Label m, (selectedRootHom A hd hs hp ho K (rootFamily A C b)).range := by
  have h : (rawHom A hd hs hp ho C K).range =
      (⨆ i, (xHom A hd hs hp ho C K i).range) ⊔
      (⨆ i, (yNegative A hd hs hp ho C K i).range) ⊔ (zHom A hd hs hp ho C K).range :=
    rawHom_range_eq_root_join A hd hs hp ho C K
  rw [h]
  simp only [iSup_sum,iSup_unique,rootFamily,xHom,zHom,yNegative_eq_selectedRootHom,sup_assoc]

end SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergCharTwoRootRange
