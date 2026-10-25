import SymmetricSubgroupAsymptotics.QuaternaryPauliMatrices
import SymmetricSubgroupAsymptotics.CFSGHeisenbergCoordinateGroup
import Mathlib.Tactic.FinCases

/-! A faithful literal degree-three representation of the coordinate
Heisenberg27 in F4 matrices. Multiplication is proved by one supported
matrix entry and a scalar character identity, not by enumerating group
pairs, matrices, subgroups or actions. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.QuaternaryPauliHeisenbergRepresentation
open CFSGHeisenbergCoordinateGroup BinaryQuadraticField
abbrev K := Scalar
abbrev P := ZMod 3
abbrev Mat := Matrix P P K
abbrev Heis := Element P 1

def character (t : P) : K := omega^t.val

theorem character_zero : character 0=1 := by decide +kernel
theorem character_add : ∀ x y : P, character (x+y)=character x*character y := by
  decide +kernel

theorem character_ne_zero : ∀ t : P, character t≠0 := by decide +kernel
theorem character_injective : Function.Injective character := by decide +kernel

def monomial (a b c : P) : Mat := fun i j =>
  if i=j+a then character (c+b*j) else 0

private theorem monomial_mul (a b c a' b' c' : P) :
    monomial a b c*monomial a' b' c'=
      monomial (a+a') (b+b') (c+c'+b*a') := by
  funext i j
  rw [Matrix.mul_apply,Finset.sum_eq_single (j+a')]
  · have he : (j+a')+a=j+(a+a') := by ring
    have hc : character (c+b*(j+a'))*character (c'+b'*j)=
        character ((c+c'+b*a')+(b+b')*j) := by
      rw [←character_add]
      congr 1
      ring
    simp only [monomial,he]
    split_ifs <;> simp_all
  · intro k _ hk
    have he : k≠j+a' := hk
    simp only [monomial,if_neg he,mul_zero]
  · simp

def matrixHom : Heis →* Mat where
  toFun g := monomial (g.a 0) (g.b 0) g.c
  map_one' := by
    change monomial 0 0 0=1
    funext i j
    simp [monomial,character_zero,Matrix.one_apply]
  map_mul' g h := by
    change monomial (g.a 0+h.a 0) (g.b 0+h.b 0) (g.c+h.c+dot g.b h.a)=
      monomial (g.a 0) (g.b 0) g.c*monomial (h.a 0) (h.b 0) h.c
    simpa only [dot,Fin.sum_univ_one] using
      (monomial_mul (g.a 0) (g.b 0) g.c (h.a 0) (h.b 0) h.c).symm

def representation : Heis →* Matˣ where
  toFun g :=
    { val := matrixHom g
      inv := matrixHom g⁻¹
      val_inv := by rw [←map_mul,mul_inv_cancel,map_one]
      inv_val := by rw [←map_mul,inv_mul_cancel,map_one] }
  map_one' := Units.ext (matrixHom.map_one)
  map_mul' g h := Units.ext (matrixHom.map_mul g h)

theorem representation_matrix (g : Heis) :
    (representation g : Mat)=monomial (g.a 0) (g.b 0) g.c := rfl

private theorem monomial_injective : Function.Injective (fun g : Heis => matrixHom g) := by
  intro g h he
  have h0 := congrFun (congrFun he (g.a 0)) 0
  change (if g.a 0=0+g.a 0 then character (g.c+g.b 0*0) else 0)=
    (if g.a 0=0+h.a 0 then character (h.c+h.b 0*0) else 0) at h0
  simp only [zero_add,mul_zero,add_zero] at h0
  have ha : g.a 0=h.a 0 := by
    by_contra hh
    rw [if_neg hh] at h0
    exact character_ne_zero g.c h0
  have hc : g.c=h.c := by
    rw [if_pos ha] at h0
    exact character_injective h0
  have h1 := congrFun (congrFun he (1+g.a 0)) 1
  change (if 1+g.a 0=1+g.a 0 then character (g.c+g.b 0*1) else 0)=
    (if 1+g.a 0=1+h.a 0 then character (h.c+h.b 0*1) else 0) at h1
  rw [ha] at h1
  simp only [mul_one] at h1
  have hb : g.b 0=h.b 0 := by
    have hh := character_injective h1
    rw [hc] at hh
    exact add_left_cancel hh
  apply Element.ext
  · funext i
    fin_cases i
    exact ha
  · funext i
    fin_cases i
    exact hb
  · exact hc

theorem representation_injective : Function.Injective representation := by
  intro g h he
  exact monomial_injective (congrArg Units.val he)

theorem range_card_twentySeven : Nat.card representation.range=27 := by
  change Nat.card (Set.range representation)=27
  rw [Nat.card_range_of_injective representation_injective,CFSGHeisenbergCoordinateGroup.card]
  norm_num

theorem central_matrix (t : P) :
    (representation (central (m := 1) (Multiplicative.ofAdd t)) : Mat)=character t • (1:Mat) := by
  change monomial 0 0 t=character t • (1:Mat)
  funext i j
  simp [monomial,Matrix.one_apply,Matrix.smul_apply]

end SymmetricSubgroupAsymptotics.QuaternaryPauliHeisenbergRepresentation
