import SymmetricSubgroupAsymptotics.FiniteMonoidGeneratedUnitsEquivalence
import SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators

/-! Matrix specialization of the finite-monoid unit-closure equivalence.
The source arrays and actual decoded matrix values are retained explicitly.
The finite-field case needs no supplied invertibility of either raw array.
No upstream model, seed parser, or named sporadic equivalence is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MatrixSeedMonoidUnitsEquivalence

open FiniteMonoidGeneratedUnitsEquivalence

/-- The positive-word monoid in the SAME two literal native matrices. -/
def seedMonoid (p n : ℕ) (a b : Array String) :
    Submonoid (Matrix (Fin n) (Fin n) (ZMod p)) :=
  Submonoid.closure ({CFSG.Models.MatrixData.matrix p n a,
    CFSG.Models.MatrixData.matrix p n b} : Set (Matrix (Fin n) (Fin n) (ZMod p)))

private theorem unitSeeds_pair_eq (p n : ℕ) (a b : Array String) :
    unitSeeds ({CFSG.Models.MatrixData.matrix p n a,
      CFSG.Models.MatrixData.matrix p n b} : Set (Matrix (Fin n) (Fin n) (ZMod p))) =
      CFSG.Models.MatrixData.generators p n a b := by
  ext u
  simp only [unitSeeds, CFSG.Models.MatrixData.generators,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Actual native positive-monoid units and the actual old GL-subgroup
closure, with no invertibility hypotheses on the two literal matrices. -/
def equiv (p n : ℕ) [NeZero p] (a b : Array String) :
    (seedMonoid p n a b)ˣ ≃* CFSG.Models.MatrixData.Model p n a b :=
  (equiv_finite ({CFSG.Models.MatrixData.matrix p n a,
    CFSG.Models.MatrixData.matrix p n b} : Set (Matrix (Fin n) (Fin n) (ZMod p)))).trans
      (MulEquiv.subgroupCongr (congrArg Subgroup.closure (unitSeeds_pair_eq p n a b)))

/-- The actual matrix, rather than merely its label or order, is preserved. -/
theorem equiv_value (p n : ℕ) [NeZero p] (a b : Array String)
    (x : (seedMonoid p n a b)ˣ) :
    (((equiv p n a b x : CFSG.Models.MatrixData.Model p n a b) :
      Matrix.GeneralLinearGroup (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) =
        ((x : seedMonoid p n a b) : Matrix (Fin n) (Fin n) (ZMod p)) := by
  rfl

/-- A decoder bridge can use this only after proving both actual matrix
identities. These are semantic seed equalities, not model-recognition inputs. -/
def equiv_of_decoded_eq (p n : ℕ) [NeZero p] (a b : Array String)
    (A B : Matrix (Fin n) (Fin n) (ZMod p))
    (hA : A = CFSG.Models.MatrixData.matrix p n a)
    (hB : B = CFSG.Models.MatrixData.matrix p n b) :
    (Submonoid.closure ({A, B} : Set (Matrix (Fin n) (Fin n) (ZMod p))))ˣ ≃*
      CFSG.Models.MatrixData.Model p n a b := by
  subst A
  subst B
  exact equiv p n a b

/-- The displayed decoder equalities are respected at the level of each
actual element under the resulting equivalence. -/
theorem equiv_of_decoded_eq_value (p n : ℕ) [NeZero p] (a b : Array String)
    (A B : Matrix (Fin n) (Fin n) (ZMod p))
    (hA : A = CFSG.Models.MatrixData.matrix p n a)
    (hB : B = CFSG.Models.MatrixData.matrix p n b)
    (x : (Submonoid.closure ({A, B} : Set (Matrix (Fin n) (Fin n) (ZMod p))))ˣ) :
    (((equiv_of_decoded_eq p n a b A B hA hB x : CFSG.Models.MatrixData.Model p n a b) :
      Matrix.GeneralLinearGroup (Fin n) (ZMod p)) : Matrix (Fin n) (Fin n) (ZMod p)) =
        ((x : Submonoid.closure ({A, B} : Set (Matrix (Fin n) (Fin n) (ZMod p)))) :
          Matrix (Fin n) (Fin n) (ZMod p)) := by
  subst A
  subst B
  exact equiv_value p n a b x

/-- Existing two-fibre generation forces raw invertibility in the old
noncommutative matrix model. No data-audit or inverse certificate is used. -/
theorem raw_seeds_isUnit_of_noncommutative (p n : ℕ) (a b : Array String)
    (hn : ¬IsMulCommutative (CFSG.Models.MatrixData.Model p n a b)) :
    IsUnit (CFSG.Models.MatrixData.matrix p n a) ∧
      IsUnit (CFSG.Models.MatrixData.matrix p n b) := by
  obtain ⟨x, hx, y, hy, hxa, hyb, hgen⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  exact ⟨hxa ▸ x.isUnit, hyb ▸ y.isUnit⟩

/-- The same conclusion follows from noncommutativity of the positive-word
unit group, using the actual equivalence rather than a name-based transfer. -/
theorem raw_seeds_isUnit_of_noncommutative_monoid_units (p n : ℕ) [NeZero p]
    (a b : Array String) (hn : ¬IsMulCommutative ((seedMonoid p n a b)ˣ)) :
    IsUnit (CFSG.Models.MatrixData.matrix p n a) ∧
      IsUnit (CFSG.Models.MatrixData.matrix p n b) := by
  apply raw_seeds_isUnit_of_noncommutative p n a b
  intro hc
  letI : IsMulCommutative (CFSG.Models.MatrixData.Model p n a b) := hc
  apply hn
  apply IsMulCommutative.of_comm
  intro x y
  apply (equiv p n a b).injective
  rw [map_mul, map_mul]
  exact mul_comm' _ _

end SymmetricSubgroupAsymptotics.MatrixSeedMonoidUnitsEquivalence
