import SymmetricSubgroupAsymptotics.CFSGRankOneBruhatClosure

/-! Rank-one Bruhat closure when the Weyl square lies in the torus.
Unlike the involution variant, this retains the actual Weyl word in
odd characteristic without replacing it by a quotient involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRankOneBruhatSquareTorus
open CFSGRankOneBruhat
variable {G : Type*} [Group G]

private def rightStabilizer (C : Set G) : Subgroup G where
  carrier := {x | (∀g∈C,g*x∈C) ∧ (∀g∈C,g*x⁻¹∈C)}
  one_mem' := by constructor <;> intro g hg <;> simpa using hg
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro g hg
      simpa only [mul_assoc] using hy.1 (g*x) (hx.1 g hg)
    · intro g hg
      simpa only [mul_inv_rev,mul_assoc] using hx.2 (g*y⁻¹) (hy.2 g hg)
  inv_mem' := by
    intro x hx
    constructor
    · exact hx.2
    · intro g hg
      simpa only [inv_inv] using hx.1 g hg

theorem closure_le_two_cells (B U T : Subgroup G) (w : G)
    (hUB : U≤B) (hTB : T≤B) (hB : B≤U⊔T)
    (hTN : T≤Subgroup.normalizer (U : Set G))
    (hWT : ∀t∈T,w*t*w⁻¹∈T) (hww : w*w∈T)
    (hWU : ∀u∈U,Cell B U w (w*u*w)) :
    ∀g∈Subgroup.closure ((B : Set G)∪{w}),Cell B U w g := by
  let C : Set G := {g | Cell B U w g}
  let D : Subgroup G := rightStabilizer C
  have hUD : U≤D := by
    intro u hu
    exact ⟨fun g hg=>cell_right_unipotent B U w hUB u g hu hg,
      fun g hg=>cell_right_unipotent B U w hUB u⁻¹ g (U.inv_mem hu) hg⟩
  have hTD : T≤D := by
    intro t ht
    exact ⟨fun g hg=>cell_right_torus B U T w hTB hTN hWT t g ht hg,
      fun g hg=>cell_right_torus B U T w hTB hTN hWT t⁻¹ g (T.inv_mem ht) hg⟩
  have hwD : w∈D := by
    constructor
    · exact fun g hg=>cell_right_weyl B U w hWU g hg
    · intro g hg
      have hh := cell_right_torus B U T w hTB hTN hWT (w*w)⁻¹ (g*w)
        (T.inv_mem hww) (cell_right_weyl B U w hWU g hg)
      have hi : w⁻¹=w*(w*w)⁻¹ := by group
      simpa only [hi,mul_assoc] using hh
  have hBD : B≤D := hB.trans (sup_le hUD hTD)
  have hle : Subgroup.closure ((B : Set G)∪{w})≤D := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx|hx
    · exact hBD hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hwD
  intro g hg
  have hh := (hle hg).1 1 (Or.inl B.one_mem)
  simpa only [one_mul] using hh

end SymmetricSubgroupAsymptotics.CFSGRankOneBruhatSquareTorus
