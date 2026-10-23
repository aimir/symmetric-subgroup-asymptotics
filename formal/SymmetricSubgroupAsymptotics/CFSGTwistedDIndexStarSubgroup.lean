import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankChainLift
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveUnipotent
import SymmetricSubgroupAsymptotics.CFSGTypeAIndexReindex
import SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointRoots

/-! An actual retained-SL point-root star inside the original relative
projective model. Faithfulness of the literal chain lift pulls a central
image condition back to the SAME SL group; the star survives the quotient.
Its dimension is r-2, not the unproved r-1 lower bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDIndexStarSubgroup
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDAllRankChainLift CFSGTwistedA2FixedField
open CFSGSpecialLinearLastBlock CFSGSpecialLinearReindex CFSGTypeABlockEmbedding
open CFSGTypeAProjectivePointRoots CFSGTypeAColumnFormCoordinates CFSGTypeAIndexReindex
open CFSGTwistedDRelativeProjectiveModel CFSGTwistedDProjectiveUnipotent

theorem chainLift_entry (n : ℕ) (q : CFSG.PrimePower)
    (A : Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q)) (i j : Fin (n + 1)) :
    (chainLift n q A : Mat (q.Extension 2) (n + 2))
      (Sum.inl i.castSucc) (Sum.inl j.castSucc) = (A.val i j : q.Extension 2) := by
  change (lastBlockHom (q.Extension 2) (n + 1)
    (Matrix.SpecialLinearGroup.map (fixedField q).subtype A)).val i.castSucc j.castSucc = _
  change (blockHom (Matrix.SpecialLinearGroup.map (fixedField q).subtype A)).val
    ((lastIndex (n + 1)).symm i.castSucc) ((lastIndex (n + 1)).symm j.castSucc) = _
  rw [lastIndex_symm_right, lastIndex_symm_right]
  rfl

theorem chainLift_injective (n : ℕ) (q : CFSG.PrimePower) : Function.Injective (chainLift n q) := by
  intro A B he
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply (fixedField q).subtype.injective
  change (A.val i j : q.Extension 2) = (B.val i j : q.Extension 2)
  rw [← chainLift_entry n q A i j, ← chainLift_entry n q B i j]
  exact congrArg (fun u : (Mat (q.Extension 2) (n + 2))ˣ =>
    (u : Mat (q.Extension 2) (n + 2)) (Sum.inl i.castSucc) (Sum.inl j.castSucc)) he

def chainHom (n : ℕ) (q : CFSG.PrimePower) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) (fixedField q) →* relativeRootGroup n q where
  toFun A := ⟨chainLift n q A, chainLift_mem n q A⟩
  map_one' := Subtype.ext ((chainLift n q).map_one)
  map_mul' A B := Subtype.ext ((chainLift n q).map_mul A B)

theorem chainHom_injective (n : ℕ) (q : CFSG.PrimePower) : Function.Injective (chainHom n q) :=
  fun _ _ h => chainLift_injective n q (congrArg Subtype.val h)

abbrev StarCoordinates (s : ℕ) := Unit ⊕ Fin (s + 2)
abbrev StarSL (s : ℕ) (q : CFSG.PrimePower) :=
  Matrix.SpecialLinearGroup (StarCoordinates s) (fixedField q)
abbrev StarForms (s : ℕ) (q : CFSG.PrimePower) :=
  pointForms (firstVector (F := fixedField q) (n := Fin (s + 2)))

local instance (s : ℕ) (q : CFSG.PrimePower) : CommGroup (Multiplicative (StarForms s q)) :=
  inferInstance

def starEmbedding (s : ℕ) (q : CFSG.PrimePower) : StarSL s q →* relativeRootGroup (s + 2) q :=
  (chainHom (s + 2) q).comp
    (slReindex (F := fixedField q) (splitCoordinates (s + 2))).toMonoidHom

theorem starEmbedding_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (starEmbedding s q) :=
  (chainHom_injective (s + 2) q).comp (slReindex (F := fixedField q) (splitCoordinates (s + 2))).injective

theorem firstVector_nonzero (s : ℕ) (q : CFSG.PrimePower) :
    firstVector (F := fixedField q) (n := Fin (s + 2)) ≠ 0 := by
  intro he
  have h := congrArg (fun v : StarCoordinates s → fixedField q => v (Sum.inl ())) he
  simp only [firstVector, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at h

def starHom (s : ℕ) (q : CFSG.PrimePower) : Multiplicative (StarForms s q) →* Projective s q :=
  ((QuotientGroup.mk' (Subgroup.center (relativeRootGroup (s + 2) q))).comp
    (starEmbedding s q)).comp (pointRootSLHom (firstVector (F := fixedField q) (n := Fin (s + 2))))

theorem starHom_injective (s : ℕ) (q : CFSG.PrimePower) : Function.Injective (starHom s q) := by
  apply (MonoidHom.ker_eq_bot_iff (starHom s q)).mp
  apply bot_unique
  intro f hf
  have hc : starEmbedding s q (pointRootSLHom firstVector f) ∈
      Subgroup.center (relativeRootGroup (s + 2) q) := (QuotientGroup.eq_one_iff _).mp hf
  have hs : pointRootSLHom firstVector f ∈ Subgroup.center (StarSL s q) := by
    apply Subgroup.mem_center_iff.mpr
    intro A
    apply starEmbedding_injective s q
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hc) (starEmbedding s q A)
  have he := pointRootSL_eq_one_of_mem_center (firstVector_nonzero s q) f hs
  have hp : pointRootHom firstVector f = 1 := by
    change projection (pointRootSLHom firstVector f) = 1
    rw [he, map_one]
  exact (Subgroup.mem_bot).mpr
    (pointRootHom_injective (firstVector_nonzero s q) (hp.trans (map_one (pointRootHom firstVector)).symm))

def starRoot (s : ℕ) (q : CFSG.PrimePower) : Subgroup (Projective s q) := (starHom s q).range

def starRootEquiv (s : ℕ) (q : CFSG.PrimePower) :
    Multiplicative (StarForms s q) ≃* starRoot s q := MonoidHom.ofInjective (starHom_injective s q)

theorem starRoot_card (s : ℕ) (q : CFSG.PrimePower) :
    Nat.card (starRoot s q) = q.order ^ (s + 2) := by
  calc
    Nat.card (starRoot s q) = Nat.card (Multiplicative (StarForms s q)) :=
      Nat.card_congr (starRootEquiv s q).symm.toEquiv
    _ = Nat.card (pointRoot (firstVector (F := fixedField q) (n := Fin (s + 2)))) :=
      Nat.card_congr (pointRootEquiv (firstVector_nonzero s q)).toEquiv
    _ = _ := by
      rw [pointRoot_card (firstVector_nonzero s q), Fintype.card_sum, Fintype.card_unit,
        Fintype.card_fin, fixedField_card]
      congr 1
      omega

end SymmetricSubgroupAsymptotics.CFSGTwistedDIndexStarSubgroup
