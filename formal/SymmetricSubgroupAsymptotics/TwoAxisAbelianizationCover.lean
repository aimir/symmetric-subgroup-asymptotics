import SymmetricSubgroupAsymptotics.DerivedGeneratorWords

/-! Two actual original elements provide a structural two-cyclic cover of
the original abelianization. Generator membership is an exact original
quotient relation, not a numerical head premise. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
variable {G : Type} [Group G] (a b : G)
abbrev Q := G ⧸ commutator G
abbrev q : G →* Q (G := G) := QuotientGroup.mk' (commutator G)
local instance quotient_commutative : IsMulCommutative (Q (G := G)) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
abbrev Left := Subgroup.zpowers (q a)
abbrev Right := Subgroup.zpowers (q b)

def cover : Left a × Right b →* Q (G := G) where
  toFun x := x.1.val*x.2.val
  map_one' := by simp
  map_mul' x y := by
    change (x.1.val*y.1.val)*(x.2.val*y.2.val)=
      (x.1.val*x.2.val)*(y.1.val*y.2.val)
    ac_rfl

theorem cover_surjective {ι : Type} (generators : ι → G)
    (hgen : Subgroup.closure (Set.range generators)=⊤)
    (haxes : ∀ i, q (generators i) ∈ Left a ⊔ Right b) :
    Function.Surjective (cover a b) := by
  let V := Left a ⊔ Right b
  have hle : Subgroup.closure (Set.range generators)≤V.comap q := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact haxes i
  have hV : V=⊤ := by
    apply top_unique
    intro y _hy
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (commutator G) y
    exact hle (hgen.symm ▸ Subgroup.mem_top x)
  intro y
  have hy : y∈Left a ⊔ Right b := by change y∈V; rw [hV]; trivial
  obtain ⟨x,hx,z,hz,hxz⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  exact ⟨(⟨x,hx⟩,⟨z,hz⟩),hxz⟩

end SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
