import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalUpper
import SymmetricSubgroupAsymptotics.CFSGTwistedAUpperUnipotent

/-! Actual radical elements in the literal defining-Frobenius upper
subgroup, every rank s+2 and every prime power including2. All displayed
form and scalar equations are discharged. The original fixed-source map
is the already proved SAME-source upper-unipotent injection; no derived
membership or full unitary/Sylow identification is claimed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryUpperArrays
open CFSGTwistedAUnitaryCoordinates CFSGTwistedAUnitaryParameters
open CFSGSerreOrdinaryTwists CFSGTwistedAUpperUnipotent

def parity (q : CFSG.PrimePower) (s : ℕ) : q.Extension 2 := (-1) ^ s

def middleForm (q : CFSG.PrimePower) (s : ℕ) : Mat (q.Extension 2) s :=
  -(signedReversalUnit (q.Extension 2) s : Mat (q.Extension 2) s)

def firstRow (q : CFSG.PrimePower) (s : ℕ) (v : Fin (s + 1) → q.Extension 2) :
    Fin (s + 1) → q.Extension 2 :=
  radicalRow (definingFieldAutomorphism q 2) (parity q s) (middleForm q s) v

def Condition (q : CFSG.PrimePower) (s : ℕ) (v : Fin (s + 1) → q.Extension 2)
    (b : q.Extension 2) : Prop :=
  definingFieldAutomorphism q 2 b + parity q s * b =
    -hermitianNorm (definingFieldAutomorphism q 2) (middleForm q s) v

theorem middleForm_hermitian (q : CFSG.PrimePower) (s : ℕ) :
    (middleForm q s).map (definingFieldAutomorphism q 2) =
      parity q s • (middleForm q s).transpose := by
  exact signedMiddle_hermitian (q.Extension 2)
    (definingFieldAutomorphism q 2).toRingHom s

theorem condition_exists (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) : ∃ b, Condition q s v b :=
  exists_block_parameter q (parity q s) (neg_one_pow_eq_or (q.Extension 2) s)
    (middleForm q s) (middleForm_hermitian q s) v

theorem naturalUpperUnit_fixed (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (b : q.Extension 2) (hb : Condition q s v b) :
    diagramFieldUnitHom (q.Extension 2) (s + 2)
      (definingFieldAutomorphism q 2).toRingHom
      (naturalUpperUnit (q.Extension 2) s (firstRow q s v) v b) =
        naturalUpperUnit (q.Extension 2) s (firstRow q s v) v b := by
  have hblock := radicalArray_isometry (definingFieldAutomorphism q 2)
    (fun a => extension_two_pow_twice q a) (parity q s)
    (neg_one_pow_eq_or (q.Extension 2) s) (middleForm q s) (middleForm_hermitian q s) v b hb
  have hFin := reindex_isometry (splitEquiv s) (definingFieldAutomorphism q 2).toRingHom
    (blockForm (parity q s) (middleForm q s))
    (upperArray (firstRow q s v) v b) hblock
  dsimp only [parity, middleForm] at hFin
  rw [blockForm_reindex] at hFin
  apply unit_fixed_of_signedForm (q.Extension 2) (s + 2)
    (definingFieldAutomorphism q 2).toRingHom
  simpa only [naturalUpperUnit_val] using hFin

def radicalElement (q : CFSG.PrimePower) (s : ℕ) (v : Fin (s + 1) → q.Extension 2)
    (b : q.Extension 2) (hb : Condition q s v b) : naturalUnipotent (s + 2) q :=
  ⟨naturalUpperElement (q.Extension 2) s (firstRow q s v) v b,
    ⟨naturalUpperElement_upper (q.Extension 2) s (firstRow q s v) v b,
      naturalUpperUnit_fixed q s v b hb⟩⟩

theorem radicalElement_matrix (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) (b : q.Extension 2) (hb : Condition q s v b) :
    ((radicalElement q s v b hb).val.val : Mat (q.Extension 2) (s + 2)) =
      Matrix.reindex (splitEquiv s) (splitEquiv s) (upperArray (firstRow q s v) v b) :=
  naturalUpperUnit_val (q.Extension 2) s (firstRow q s v) v b

theorem exists_radicalElement_matrix (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin (s + 1) → q.Extension 2) :
    ∃ g : naturalUnipotent (s + 2) q, ∃ b : q.Extension 2,
      (g.val.val : Mat (q.Extension 2) (s + 2)) =
        Matrix.reindex (splitEquiv s) (splitEquiv s) (upperArray (firstRow q s v) v b) := by
  obtain ⟨b, hb⟩ := condition_exists q s v
  exact ⟨radicalElement q s v b hb, b, radicalElement_matrix q s v b hb⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalRadical
