import SymmetricSubgroupAsymptotics.DihedralNormalGenerators

/-! Actual normal subgroups whose underlying groups embed in D8 need two
ambient normal generators. The injection can be the actual monomial
section action-kernel/block map; no normality in D8 is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.DihedralEightInjectedNormalGenerators
open MarkedC4

/-- Ordinary generation is bounded for every actual injected group, not
merely for ambient-normal subgroups of the displayed dihedral model. -/
theorem genRank_le_two {H : Type} [Group H] [Finite H]
    (f : H →* DihedralGroup 4) (hf : Function.Injective f) : genRank H≤2 := by
  let q := (DihedralNormalGenerators.parity 4).comp f
  let k : q.ker →* (DihedralNormalGenerators.parity 4).ker :=
    (f.comp q.ker.subtype).codRestrict _ (fun x => x.property)
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    exact hf (congrArg Subtype.val he)
  letI := DihedralNormalGenerators.parity_ker_isCyclic 4
  letI : IsCyclic q.ker := isCyclic_of_injective k hk
  letI : IsCyclic (H ⧸ q.ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift q) (QuotientGroup.kerLift_injective q)
  calc
    genRank H≤genRank q.ker+genRank (H ⧸ q.ker) := genRank_le_of_normal q.ker
    _≤1+1 := Nat.add_le_add genRank_le_one_of_isCyclic genRank_le_one_of_isCyclic
    _=2 := rfl

/-- Applies to the literal binary normal row of the residual acting kernel.
Its injection into D8 suffices, even when its image is not D8-normal. -/
theorem normalGen_le_two {G : Type} [Group G] [Finite G]
    (M : Subgroup G) [M.Normal]
    (f : M →* DihedralGroup 4) (hf : Function.Injective f) : normalGen M≤2 := by
  obtain ⟨S,hcard,hclosure⟩ := genRank_spec (G := M)
  let T : Finset G := S.image M.subtype
  have hsub : (T : Set G)⊆M := by
    rintro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hcl : Subgroup.closure (T : Set G)=M := by
    calc
      _=(Subgroup.closure (S : Set M)).map M.subtype := by
        rw [MonoidHom.map_closure,Finset.coe_image]
      _=M := by rw [hclosure,← MonoidHom.range_eq_map,Subgroup.range_subtype]
  have hn : Subgroup.normalClosure (T : Set G)=M := by
    apply le_antisymm (Subgroup.normalClosure_le_normal hsub)
    rw [← hcl]
    exact Subgroup.closure_le_normalClosure
  calc
    normalGen M≤T.card := normalGen_le hsub hn
    _≤S.card := Finset.card_image_le
    _=genRank M := hcard
    _≤2 := genRank_le_two f hf

end SymmetricSubgroupAsymptotics.DihedralEightInjectedNormalGenerators
