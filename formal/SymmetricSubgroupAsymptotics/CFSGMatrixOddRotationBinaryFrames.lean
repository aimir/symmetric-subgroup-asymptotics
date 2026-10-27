import SymmetricSubgroupAsymptotics.CFSGOddRotationBinaryFrames
import SymmetricSubgroupAsymptotics.NoncommutativeTwoFibreGenerators

/-! Positive whole-matrix certificate interface for the SAME literal
MatrixData model. Noncommutativity supplies genuine original units in both
literal matrix fibres. B^3=1 justifies B^-1=B^2 in those actual units.
No whole power, source invertibility or generation claim is inferred from
selected rows/vectors, numerical output, or a name-based model transfer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixOddRotationBinaryFrames
open CFSG.Models CFSGReduction

theorem matrix_model_goodSylowTwo_of_odd_rotation
    (hCFSG : CFSG.CFSGClassification) (p n : ℕ) (a b : Array String)
    [Finite (MatrixData.Model p n a b)]
    (hn : ¬IsMulCommutative (MatrixData.Model p n a b)) (m k : ℕ)
    (ha : (MatrixData.matrix p n a)^2=1)
    (hb : (MatrixData.matrix p n b)^3=1)
    (hr : (MatrixData.matrix p n a*(MatrixData.matrix p n b)^2*
      MatrixData.matrix p n a*MatrixData.matrix p n b)^(2*m+1)=1)
    (hc : ((MatrixData.matrix p n a*(MatrixData.matrix p n b)^2*
      MatrixData.matrix p n a*MatrixData.matrix p n b)^(m+1)*
      (MatrixData.matrix p n b)^2)^(2^k)=1) :
    GoodSylowPrime (MatrixData.Model p n a b) 2 := by
  obtain ⟨x,hx,y,hy,hxa,hyb,hgen⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  let C := Subgroup.closure (MatrixData.generators p n a b)
  let xm : C := ⟨x,Subgroup.subset_closure hx⟩
  let ym : C := ⟨y,Subgroup.subset_closure hy⟩
  let rho : C →* Matrix (Fin n) (Fin n) (ZMod p) := (Units.coeHom _).comp C.subtype
  have hinj : Function.Injective rho := by
    intro u v he
    apply Subtype.ext
    exact Units.ext he
  have hxm : rho xm=MatrixData.matrix p n a := hxa
  have hym : rho ym=MatrixData.matrix p n b := hyb
  have hxm2 : xm^2=1 := by
    apply hinj
    rw [map_pow,map_one,hxm]
    exact ha
  have hym3 : ym^3=1 := by
    apply hinj
    rw [map_pow,map_one,hym]
    exact hb
  have hymInv : ym⁻¹=ym^2 := by
    apply inv_eq_of_mul_eq_one_right
    exact (pow_succ' ym 2).symm.trans hym3
  have hrotation : rho (xm*(ym⁻¹*xm*ym))=
      MatrixData.matrix p n a*(MatrixData.matrix p n b)^2*
        MatrixData.matrix p n a*MatrixData.matrix p n b := by
    simp only [hymInv,map_mul,map_pow,hxm,hym,mul_assoc]
  have hbray : rho (CFSGOddRotationBinaryFrames.brayElement xm ym m)=
      (MatrixData.matrix p n a*(MatrixData.matrix p n b)^2*
        MatrixData.matrix p n a*MatrixData.matrix p n b)^(m+1)*
          (MatrixData.matrix p n b)^2 := by
    simp only [CFSGOddRotationBinaryFrames.brayElement,hymInv,map_mul,map_pow,hxm,hym,mul_assoc]
  have hrotpow : (xm*(ym⁻¹*xm*ym))^(2*m+1)=1 := by
    apply hinj
    rw [map_pow,map_one,hrotation]
    exact hr
  have hbraypow : (CFSGOddRotationBinaryFrames.brayElement xm ym m)^(2^k)=1 := by
    apply hinj
    rw [map_pow,map_one,hbray]
    exact hc
  have hgenC : Subgroup.closure ({xm,ym} : Set C)=⊤ := by
    let H : Subgroup C := Subgroup.closure ({xm,ym} : Set C)
    have hCH : C≤H.map C.subtype := by
      change Subgroup.closure (MatrixData.generators p n a b)≤H.map C.subtype
      rw [←hgen]
      apply (Subgroup.closure_le _).mpr
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact ⟨xm,Subgroup.subset_closure (Set.mem_insert _ _),rfl⟩
      · have he : z=y := Set.mem_singleton_iff.mp hz
        subst z
        exact ⟨ym,Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl),rfl⟩
    apply top_unique
    intro z _
    obtain ⟨w,hw,he⟩ := hCH z.property
    have hwz : w=z := Subtype.ext he
    exact hwz ▸ hw
  exact CFSGOddRotationBinaryFrames.goodSylowPrime hCFSG xm ym m k hxm2 hrotpow hbraypow hgenC

end SymmetricSubgroupAsymptotics.CFSGMatrixOddRotationBinaryFrames
