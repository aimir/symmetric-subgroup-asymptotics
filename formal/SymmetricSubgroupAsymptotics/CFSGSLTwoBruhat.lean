import SymmetricSubgroupAsymptotics.CFSGPSLTwoRootCoordinates

/-! Literal two-cell coordinates in SL2 over the original arbitrary
field. The big-cell Borel coordinate is obtained by actual matrix
multiplication; no group order or projective recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSLTwoBruhat
open Matrix CFSGTypeASLTwoWeyl CFSGTypeARootTorus CFSGSLTwoUpperRoots
open CFSGPSLTwoRootCoordinates
variable {F : Type*} [Field F]

def torusHom : Fˣ →* SL2 (F:=F) where
  toFun := torus (by decide : (0 : Fin 2)≠1)
  map_one' := by
    apply Subtype.ext
    rw [torus_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' c d := by
    apply Subtype.ext
    change (torus (by decide : (0 : Fin 2)≠1) (c*d)).val=
      (torus (by decide : (0 : Fin 2)≠1) c).val*
        (torus (by decide : (0 : Fin 2)≠1) d).val
    rw [torus_coe,torus_coe,torus_coe,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [_root_.mul_inv_rev,mul_comm]

theorem torus_mem_borel (c : Fˣ) : torusHom c∈borel (F:=F) := by
  change (torus (by decide : (0 : Fin 2)≠1) c).val 1 0=0
  rw [torus_coe]
  simp

theorem borel_factor (g : SL2 (F:=F)) (hg : g∈borel (F:=F)) :
    ∃ (c : Fˣ) (a : F),g=torusHom c*upper a := by
  have hg10 : g.val 1 0=0 := hg
  let c : Fˣ := diagonal ⟨g,hg⟩
  have hc0 : (c : F)=g.val 0 0 := rfl
  have hc1 : (c : F)⁻¹=g.val 1 1 := (Units.val_inv_eq_inv_val c).symm
  have hg00 : g.val 0 0≠0 := hc0 ▸ Units.ne_zero c
  have hg11 : g.val 1 1=(g.val 0 0)⁻¹ := by
    rw [←hc0]
    exact hc1.symm
  refine ⟨c,(c : F)⁻¹*g.val 0 1,?_⟩
  apply Subtype.ext
  change g.val=(torus (by decide : (0 : Fin 2)≠1) c).val*
    (upper ((c : F)⁻¹*g.val 0 1)).val
  rw [torus_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,upper_entry00,upper_entry01,upper_entry10,
      upper_entry11,hc0,hg00,hg11,hg10]

theorem torus_conjugate_mem_upper (c : Fˣ) (g : SL2 (F:=F))
    (hg : g∈upperRoot (F:=F)) :
    torusHom c*g*(torusHom c)⁻¹∈upperRoot (F:=F) := by
  obtain ⟨a,rfl⟩ := hg
  change torus (by decide : (0 : Fin 2)≠1) c*
    CFSGTypeAElementaryMatrices.elementary (by decide : (0 : Fin 2)≠1) a.toAdd*
    (torus (by decide : (0 : Fin 2)≠1) c)⁻¹∈upperRoot
  rw [torus_conjugation]
  exact upper_mem _

theorem torus_normalizes_upper (c : Fˣ) :
    torusHom c∈Subgroup.normalizer (upperRoot (F:=F) : Set (SL2 (F:=F))) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  constructor
  · exact torus_conjugate_mem_upper c g
  · intro hg
    have hh := torus_conjugate_mem_upper c⁻¹ _ hg
    rw [map_inv] at hh
    simpa [mul_assoc] using hh

theorem borel_le_normalizer_upper :
    borel (F:=F)≤Subgroup.normalizer (upperRoot (F:=F) : Set (SL2 (F:=F))) := by
  intro g hg
  obtain ⟨c,a,rfl⟩ := borel_factor g hg
  exact (Subgroup.normalizer _).mul_mem (torus_normalizes_upper c)
    (Subgroup.le_normalizer (upper_mem a))

theorem normalizer_upper_eq_borel :
    Subgroup.normalizer (upperRoot (F:=F) : Set (SL2 (F:=F)))=borel (F:=F) :=
  le_antisymm normalizer_le_borel borel_le_normalizer_upper

theorem bigCell_coordinate_mem_borel (g : SL2 (F:=F)) (hc : g.val 1 0≠0) :
    g*upper (-(g.val 1 1/g.val 1 0))*(weyl (F:=F))⁻¹∈borel (F:=F) := by
  change ((g.val*(upper (-(g.val 1 1/g.val 1 0))).val*(weyl⁻¹).val) :
    Matrix (Fin 2) (Fin 2) F) 1 0=0
  rw [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,sl_weyl_coe]
  simp [Matrix.mul_apply,Fin.sum_univ_two,upper_entry00,upper_entry01,
    upper_entry10,upper_entry11]
  field_simp [hc]
  simp

theorem two_cells (g : SL2 (F:=F)) :
    g∈borel (F:=F) ∨ ∃ (b : borel (F:=F)) (u : upperRoot (F:=F)),
      g=b.val*weyl*u.val := by
  by_cases hc : g.val 1 0=0
  · exact Or.inl hc
  · let t : F := g.val 1 1/g.val 1 0
    let b : SL2 (F:=F) := g*upper (-t)*weyl⁻¹
    have hb : b∈borel (F:=F) := bigCell_coordinate_mem_borel g hc
    have hcancel : upper (-t)*upper t=(1 : SL2 (F:=F)) := by
      change upperHom (Multiplicative.ofAdd (-t))*upperHom (Multiplicative.ofAdd t)=1
      rw [←map_mul]
      simp
    refine Or.inr ⟨⟨b,hb⟩,⟨upper t,upper_mem t⟩,?_⟩
    change g=b*weyl*upper t
    symm
    calc
      b*weyl*upper t=g*(upper (-t)*upper t) := by dsimp [b]; group
      _ = g := by rw [hcancel,mul_one]

end SymmetricSubgroupAsymptotics.CFSGSLTwoBruhat
