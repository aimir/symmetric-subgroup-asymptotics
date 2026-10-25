import SymmetricSubgroupAsymptotics.QuaternaryPauliHeisenbergRepresentation
import SymmetricSubgroupAsymptotics.QuaternaryUnitarySymplecticEmbedding

/-! The SAME faithful Pauli27 representation lies in the ACTUAL F4
unitary subgroup, and hence in the literal binary symplectic group.
The Fourier and phase elements are the checked displayed matrices.
No group order, splitting, model recognition or index is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.QuaternaryPauliUnitaryRepresentation
open CFSGHeisenbergCoordinateGroup QuaternaryPauliHeisenbergRepresentation

private theorem character_norm : ∀ t : P,
    QuaternaryUnitarySymplecticEmbedding.squaring (character t)*character t=1 := by
  decide +kernel

private theorem monomial_unitary (a b c : P) :
    QuaternaryUnitarySymplecticEmbedding.adjoint P (monomial a b c)*monomial a b c=1 := by
  funext i j
  rw [Matrix.mul_apply,Finset.sum_eq_single (j+a)]
  · change QuaternaryUnitarySymplecticEmbedding.squaring (monomial a b c (j+a) i)*
        monomial a b c (j+a) j=(1:Mat) i j
    rw [show monomial a b c (j+a) j=character (c+b*j) by simp [monomial]]
    by_cases h : i=j
    · subst j
      rw [show monomial a b c (i+a) i=character (c+b*i) by simp [monomial]]
      simpa only [Matrix.one_apply,if_pos rfl] using character_norm (c+b*i)
    · have he : j+a≠i+a := fun hh => h (add_right_cancel hh).symm
      rw [show monomial a b c (j+a) i=0 by simp [monomial,he],map_zero,zero_mul]
      simp [Matrix.one_apply,h]
  · intro k _ hk
    change QuaternaryUnitarySymplecticEmbedding.squaring (monomial a b c k i)*
      monomial a b c k j=0
    rw [show monomial a b c k j=0 by simp [monomial,hk],mul_zero]
  · simp

def representation : Heis →* QuaternaryUnitarySymplecticEmbedding.unitary P where
  toFun g := ⟨QuaternaryPauliHeisenbergRepresentation.representation g,
    monomial_unitary (g.a 0) (g.b 0) g.c⟩
  map_one' := Subtype.ext QuaternaryPauliHeisenbergRepresentation.representation.map_one
  map_mul' g h := Subtype.ext
    (QuaternaryPauliHeisenbergRepresentation.representation.map_mul g h)

theorem representation_injective : Function.Injective representation := by
  intro g h he
  exact QuaternaryPauliHeisenbergRepresentation.representation_injective
    (congrArg Subtype.val he)

def binaryRepresentation : Heis →* Matrix.symplecticGroup P (ZMod 2) :=
  (QuaternaryUnitarySymplecticEmbedding.symplecticHom P).comp representation

theorem binaryRepresentation_injective : Function.Injective binaryRepresentation :=
  (QuaternaryUnitarySymplecticEmbedding.symplecticHom_injective P).comp representation_injective

def fourier : QuaternaryUnitarySymplecticEmbedding.unitary P :=
  ⟨QuaternaryPauliMatrices.fourier,QuaternaryPauliMatrices.unitary_matrices.2.2.1⟩

def phase : QuaternaryUnitarySymplecticEmbedding.unitary P :=
  ⟨QuaternaryPauliMatrices.phase,QuaternaryPauliMatrices.unitary_matrices.2.2.2⟩

theorem central_matrix (t : P) :
    (representation (central (m := 1) (Multiplicative.ofAdd t))).val.val=
      character t • (1:Mat) := QuaternaryPauliHeisenbergRepresentation.central_matrix t

end SymmetricSubgroupAsymptotics.QuaternaryPauliUnitaryRepresentation
