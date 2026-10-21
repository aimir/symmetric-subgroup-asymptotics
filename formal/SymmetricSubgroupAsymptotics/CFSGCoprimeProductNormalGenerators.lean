import SymmetricSubgroupAsymptotics.MarkedC4CoprimePhysicalGrid
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-! Pair normal generators across coprime actual factors. Unlike an
additive extension estimate, this keeps the maximum of the two ambient
normal-generator numbers, including arbitrary original normal subgroups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGCoprimeProductNormalGenerators
open MarkedC4

/-- Coprimality forces the normal closure of paired tuples to be the full
actual product of their two coordinate images. No socle hypothesis occurs. -/
theorem normalGen_le_max {P O : Type} [Group P] [Group O] [Finite P] [Finite O]
    (hcop : Nat.Coprime (Nat.card P) (Nat.card O))
    (N : Subgroup (P × O)) [N.Normal] :
    normalGen N ≤ max (normalGen (N.map (MonoidHom.fst P O)))
      (normalGen (N.map (MonoidHom.snd P O))) := by
  let f : P × O →* P := MonoidHom.fst P O
  let g : P × O →* O := MonoidHom.snd P O
  have hf : Function.Surjective f := fun x => ⟨(x,1),rfl⟩
  have hg : Function.Surjective g := fun y => ⟨(1,y),rfl⟩
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  letI : (N.map g).Normal := Subgroup.Normal.map inferInstance g hg
  let t := max (normalGen (N.map f)) (normalGen (N.map g))
  obtain ⟨x,hx⟩ := exists_normal_generating_tuple_of_normalGen_le (N.map f)
    (show normalGen (N.map f) ≤ t from le_max_left _ _)
  obtain ⟨y,hy⟩ := exists_normal_generating_tuple_of_normalGen_le (N.map g)
    (show normalGen (N.map g) ≤ t from le_max_right _ _)
  let z : Fin t → P × O := fun i => (x i,y i)
  let H := Subgroup.normalClosure (Set.range z)
  have hfx : f '' Set.range z=Set.range x := by
    ext a
    constructor
    · rintro ⟨u,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨z i,⟨i,rfl⟩,rfl⟩
  have hgy : g '' Set.range z=Set.range y := by
    ext a
    constructor
    · rintro ⟨u,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨z i,⟨i,rfl⟩,rfl⟩
  have hHf : H.map f=N.map f := by
    change (Subgroup.normalClosure (Set.range z)).map f=N.map f
    rw [Subgroup.map_normalClosure _ f hf,hfx,hx]
  have hHg : H.map g=N.map g := by
    change (Subgroup.normalClosure (Set.range z)).map g=N.map g
    rw [Subgroup.map_normalClosure _ g hg,hgy,hy]
  have hHN : H=N := by
    rw [CoprimePhysicalGrid.subgroup_eq_product hcop H,
      CoprimePhysicalGrid.subgroup_eq_product hcop N]
    change (H.map f).prod (H.map g)=(N.map f).prod (N.map g)
    rw [hHf,hHg]
  exact normalGen_le_of_fin_tuple z hHN

end SymmetricSubgroupAsymptotics.CFSGCoprimeProductNormalGenerators
