import SymmetricSubgroupAsymptotics.PermutationalWreathQuotient

/-! Normal subgroups inside the actual block kernel have normal local
images. Full component and actual coarse transitivity force every image
to be nontrivial once the original subgroup is nontrivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathNormalBaseCoordinates
open PermutationalWreathProduct
variable {G D Q I : Type} [Group G] [Group D] [Group Q] [MulAction Q I]
  (rho : G →* PermutationalWreathProduct D Q I)
  (L : Subgroup G) (hL : L≤(rightHom.comp rho).ker)

def coordinate (hL : L≤(rightHom.comp rho).ker) (i : I) : L →* D where
  toFun l := (rho l.val).left i
  map_one' := by
    change (rho (1 : G)).left i=1
    rw [map_one]
    rfl
  map_mul' l m := by
    change (rho (l.val*m.val)).left i=(rho l.val).left i*(rho m.val).left i
    rw [map_mul,mul_left]
    have ht : (rho l.val).right=1 := hL l.property
    rw [ht,inv_one]
    simp only [Pi.mul_apply,one_smul]

 theorem coordinate_range_normal [L.Normal]
    (hfull : Compression.FullComponent rho) (i : I) :
    (coordinate rho L hL i).range.Normal := by
  constructor
  rintro d ⟨l,rfl⟩ c
  obtain ⟨a,ha,hac⟩ := hfull i c
  let z : L := ⟨a*l.val*a⁻¹,(inferInstance : L.Normal).conj_mem l.val l.property a⟩
  refine ⟨z,?_⟩
  change (rho (a*l.val*a⁻¹)).left i=c*(rho l.val).left i*c⁻¹
  rw [map_mul,map_mul,map_inv,conj_left_of_fixed (rho a) (rho l.val) i ha
    (show (rho l.val).right=1 from hL l.property),hac]

private theorem conjugate_coordinate (a e : PermutationalWreathProduct D Q I)
    (he : e.right=1) (i : I) :
    (a*e*a⁻¹).left (a.right • i)=
      a.left (a.right • i)*e.left i*(a.left (a.right • i))⁻¹ := by
  simp only [mul_left,mul_right,inv_left,Pi.mul_apply,Pi.inv_apply,
    he,mul_one,inv_smul_smul,smul_inv_smul]

 theorem all_coordinate_nontrivial [L.Normal]
    (hrho : Function.Injective rho)
    (htop : Function.Surjective (rightHom.comp rho))
    [MulAction.IsPretransitive Q I] (hne : L≠⊥) :
    ∀ i : I,(coordinate rho L hL i).range≠⊥ := by
  letI : Nontrivial L := L.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨l,hl⟩ := exists_ne (1 : L)
  have hsome : ∃ i : I,coordinate rho L hL i l≠1 := by
    by_contra hn
    push_neg at hn
    apply hl
    apply Subtype.ext
    apply hrho
    change rho l.val=rho (1 : G)
    rw [map_one]
    apply PermutationalWreathProduct.ext
    · funext i
      exact hn i
    · exact hL l.property
  obtain ⟨i,hi⟩ := hsome
  intro j hj
  obtain ⟨q,hq⟩ := MulAction.exists_smul_eq Q i j
  obtain ⟨a,ha⟩ := htop q
  have haj : (rho a).right • i=j := by rw [show (rho a).right=q from ha]; exact hq
  let z : L := ⟨a*l.val*a⁻¹,(inferInstance : L.Normal).conj_mem l.val l.property a⟩
  have hz : coordinate rho L hL j z=1 := by
    have hm : coordinate rho L hL j z∈(coordinate rho L hL j).range := ⟨z,rfl⟩
    rw [hj,Subgroup.mem_bot] at hm
    exact hm
  have he := conjugate_coordinate (rho a) (rho l.val)
    (show (rho l.val).right=1 from hL l.property) i
  rw [haj] at he
  have hz' : (rho a).left j*(rho l.val).left i*((rho a).left j)⁻¹=1 := by
    rw [←he,←map_inv,←map_mul,←map_mul]
    exact hz
  apply hi
  exact (MulAut.conj ((rho a).left j)).injective
    (hz'.trans (map_one (MulAut.conj ((rho a).left j))).symm)

end SymmetricSubgroupAsymptotics.WreathNormalBaseCoordinates
