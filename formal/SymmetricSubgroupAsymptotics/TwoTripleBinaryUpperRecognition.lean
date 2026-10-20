import SymmetricSubgroupAsymptotics.C2WreathNormalCoverQuotient
import Mathlib.Tactic.FinCases

/-! The eight-element binary upper of a two-triple wreath. A subgroup
with a block exchange is contained in the scalar/swap upper, contained
in the quarter-turn upper, or is the whole upper. Only explicit words in
this fixed eight-element group are checked; no subgroup census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwoTripleBinaryUpperRecognition
open SemidirectProduct
abbrev Binary := Multiplicative (ZMod 2)
abbrev Upper := C2Wreath.W Binary

private def coordinates : Upper ≃ (Binary × Binary) × Binary where
  toFun g := (g.left,g.right)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
local instance : Fintype Upper := Fintype.ofEquiv ((Binary × Binary) × Binary) coordinates.symm
local instance : DecidableEq Upper := fun a b =>
  decidable_of_iff (coordinates a = coordinates b) coordinates.injective.eq_iff

def total : Upper →* Binary where
  toFun g := g.left.1 * g.left.2
  map_one' := by decide +kernel
  map_mul' := by intro g h; revert g h; decide +kernel

def quarterCharacter : Upper →* Binary where
  toFun g := total g * g.right
  map_one' := by decide +kernel
  map_mul' := by intro g h; revert g h; decide +kernel

def candidates (x y z : Upper) : Fin 6 → Upper := ![x,y,z,x*y,x*z,y*z]

private theorem basis_from_obstructions : ∀ x y z : Upper,
    z.right = C2Wreath.gen → total x ≠ 1 → quarterCharacter y ≠ 1 →
    ∃ i j : Fin 6,
      total (candidates x y z i) = 1 ∧ (candidates x y z i).right = C2Wreath.gen ∧
      total (candidates x y z j) = C2Wreath.gen ∧ (candidates x y z j).right = 1 := by
  decide +kernel

private theorem basis_word_cover : ∀ a b g : Upper,
    total a = 1 → a.right = C2Wreath.gen →
    total b = C2Wreath.gen → b.right = 1 →
    ∃ i : Fin 4, ∃ j : Fin 2,
      coordinates ((a*b)^i.val * a^j.val) = coordinates g := by
  decide +kernel

private theorem candidates_mem (H : Subgroup Upper) (x y z : Upper)
    (hx : x ∈ H) (hy : y ∈ H) (hz : z ∈ H) : ∀ i, candidates x y z i ∈ H := by
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz
  · exact H.mul_mem hx hy
  · exact H.mul_mem hx hz
  · exact H.mul_mem hy hz

theorem subgroup_cases (H : Subgroup Upper)
    (hswap : ∃ z : Upper, z ∈ H ∧ z.right = C2Wreath.gen) :
    H ≤ total.ker ∨ H ≤ quarterCharacter.ker ∨ H = ⊤ := by
  by_cases ha : H ≤ total.ker
  · exact Or.inl ha
  by_cases hb : H ≤ quarterCharacter.ker
  · exact Or.inr (Or.inl hb)
  right
  right
  have hx : ∃ x : Upper, x ∈ H ∧ total x ≠ 1 := by
    by_contra hn
    push Not at hn
    exact ha (fun x hx => hn x hx)
  have hy : ∃ y : Upper, y ∈ H ∧ quarterCharacter y ≠ 1 := by
    by_contra hn
    push Not at hn
    exact hb (fun y hy => hn y hy)
  obtain ⟨x,hx,hxt⟩ := hx
  obtain ⟨y,hy,hyt⟩ := hy
  obtain ⟨z,hz,hzt⟩ := hswap
  obtain ⟨i,j,hi0,hi1,hj0,hj1⟩ := basis_from_obstructions x y z hzt hxt hyt
  apply top_unique
  intro g _
  obtain ⟨r,s,he⟩ := basis_word_cover (candidates x y z i) (candidates x y z j) g hi0 hi1 hj0 hj1
  have he' : (candidates x y z i*candidates x y z j)^r.val *
      (candidates x y z i)^s.val = g := coordinates.injective he
  rw [← he']
  exact H.mul_mem
    (H.pow_mem (H.mul_mem (candidates_mem H x y z hx hy hz i)
      (candidates_mem H x y z hx hy hz j)) _)
    (H.pow_mem (candidates_mem H x y z hx hy hz i) _)

end SymmetricSubgroupAsymptotics.TwoTripleBinaryUpperRecognition
