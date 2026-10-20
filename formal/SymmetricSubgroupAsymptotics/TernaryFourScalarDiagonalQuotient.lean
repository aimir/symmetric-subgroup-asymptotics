import SymmetricSubgroupAsymptotics.TernaryFourScalarFullProjection
import SymmetricSubgroupAsymptotics.TernaryScalarComplementSocles

/-! The actual diagonal quotient for an independent global sign.
Summing the four ternary coordinates gives an affine ternary line. Its
translation/sign law is identified explicitly with D3, retaining the
original complement factor and the original full-module kernel. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryFourScalarDiagonalQuotient

open SemidirectProduct

abbrev C2 := Multiplicative (ZMod 2)
abbrev D3 := DihedralGroup 3
abbrev FullVector := Fin 4 → ZMod 3

def bitScalar : C2 →* (ZMod 3)ˣ where
  toFun z := (-1) ^ z.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def dihedralCoordinate (a : ZMod 3) (z : C2) : D3 :=
  if z = 1 then DihedralGroup.r a else DihedralGroup.sr (-a)

theorem dihedralCoordinate_mul : ∀ (a c : ZMod 3) (z w : C2),
    dihedralCoordinate (a + (bitScalar z : ZMod 3)*c) (z*w) =
      dihedralCoordinate a z * dihedralCoordinate c w := by
  decide +kernel

theorem dihedralCoordinate_eq_one : ∀ (a : ZMod 3) (z : C2),
    dihedralCoordinate a z = 1 ↔ a = 0 ∧ z = 1 := by
  decide +kernel

theorem dihedralCoordinate_surjective :
    ∀ d : D3, ∃ a : ZMod 3, ∃ z : C2, dihedralCoordinate a z = d := by
  intro d
  cases d with
  | r a => exact ⟨a,1,by simp [dihedralCoordinate]⟩
  | sr a =>
    refine ⟨-a,Multiplicative.ofAdd 1,?_⟩
    have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by decide +kernel
    simp only [dihedralCoordinate,if_neg hne,neg_neg]

variable {H : Type} [Group H] (b : H →* Equiv.Perm (Fin 4))

def blocks : H × C2 →* Equiv.Perm (Fin 4) := b.comp (MonoidHom.fst H C2)

def scalars : H × C2 →* (ZMod 3)ˣ := bitScalar.comp (MonoidHom.snd H C2)

abbrev Model := TernaryFourScalarFullProjection.Model (blocks b) (scalars (H := H))

theorem sum_action (g : H × C2) (v : FullVector) :
    (∑ i, TernaryMonomialSemidirect.linearAction (blocks b) (scalars (H := H)) g v i) =
      (bitScalar g.2 : ZMod 3) * ∑ i, v i := by
  change (∑ i, (bitScalar g.2 : ZMod 3) * v (b g.1⁻¹ i)) =
    (bitScalar g.2 : ZMod 3) * ∑ i, v i
  rw [← Finset.mul_sum,Equiv.sum_comp (b g.1⁻¹) v]

theorem sum_mul_left (g h : Model b) :
    (∑ i, (g*h).left.toAdd i) =
      (∑ i, g.left.toAdd i) + (bitScalar g.right.2 : ZMod 3) * ∑ i, h.left.toAdd i := by
  change (∑ i, (g.left.toAdd i + (TernaryMonomialSemidirect.linearAction
    (blocks b) (scalars (H := H)) g.right h.left.toAdd) i)) = _
  rw [Finset.sum_add_distrib,sum_action]

def toDiagonal : Model b →* H × D3 where
  toFun g := (g.right.1,dihedralCoordinate (∑ i, g.left.toAdd i) g.right.2)
  map_one' := by
    apply Prod.ext
    · rfl
    · change dihedralCoordinate (∑ _ : Fin 4, (0 : ZMod 3)) 1 = 1
      simp [dihedralCoordinate]
  map_mul' g h := by
    apply Prod.ext
    · rfl
    · change dihedralCoordinate (∑ i, (g*h).left.toAdd i) (g.right.2*h.right.2) =
        dihedralCoordinate (∑ i, g.left.toAdd i) g.right.2 *
          dihedralCoordinate (∑ i, h.left.toAdd i) h.right.2
      rw [sum_mul_left]
      exact dihedralCoordinate_mul _ _ _ _

theorem toDiagonal_surjective : Function.Surjective (toDiagonal b) := by
  intro x
  obtain ⟨a,z,haz⟩ := dihedralCoordinate_surjective x.2
  refine ⟨⟨Multiplicative.ofAdd (Pi.single 0 a),(x.1,z)⟩,?_⟩
  apply Prod.ext
  · rfl
  · change dihedralCoordinate (∑ i : Fin 4, (Pi.single 0 a : FullVector) i) z = x.2
    simpa only [Fintype.sum_pi_single'] using haz

theorem mem_toDiagonal_ker (g : Model b) :
    g ∈ (toDiagonal b).ker ↔ g.right = 1 ∧ ∑ i, g.left.toAdd i = 0 := by
  change (g.right.1,dihedralCoordinate (∑ i, g.left.toAdd i) g.right.2) = 1 ↔ _
  rw [Prod.ext_iff]
  change (g.right.1 = 1 ∧ dihedralCoordinate (∑ i, g.left.toAdd i) g.right.2 = 1) ↔ _
  rw [dihedralCoordinate_eq_one]
  constructor
  · rintro ⟨hfirst,hsum,hsecond⟩
    exact ⟨Prod.ext hfirst hsecond,hsum⟩
  · rintro ⟨hright,hsum⟩
    exact ⟨congrArg Prod.fst hright,hsum,congrArg Prod.snd hright⟩

end SymmetricSubgroupAsymptotics.TernaryFourScalarDiagonalQuotient

end
