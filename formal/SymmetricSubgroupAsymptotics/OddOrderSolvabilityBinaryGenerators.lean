import SymmetricSubgroupAsymptotics.CFSGTwoBinaryPowerGenerators
import SymmetricSubgroupAsymptotics.CFSGMatrixOddRotationBinaryFrames
import SymmetricSubgroupAsymptotics.SylowTwoNormalizerOfOddOrderSolvability

/-! Exact checked binary-power and Bray proof bodies, isolating their sole
classification use as odd-order solvability. This argument is supplied by
internal extended-model parity in the actual AG consumer. No new public T1
input is introduced. Whole powers and actual generator recovery are retained.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddOrderSolvabilityBinaryGenerators
open CFSG.Models CFSGReduction CFSGOddRotationBinaryFrames
open CFSGCommutingBinaryFrameGeneration
open SylowTwoNormalizerOfOddOrderSolvability (OddOrderSolvability)

theorem goodSylowTwo_of_two_power_generators {G : Type} [Group G] [Finite G]
    (hodd : OddOrderSolvability) (x y : G) (k l : ℕ)
    (hx : x ^ (2 ^ k) = 1) (hy : y ^ (2 ^ l) = 1)
    (hgen : Subgroup.closure ({x, y} : Set G) = ⊤) : GoodSylowPrime G 2 := by
  apply SylowTwoNormalizerOfOddOrderSolvability.goodSylowTwo_of_two_binary_subgroups hodd
    (Subgroup.zpowers x) (Subgroup.zpowers y)
    (zpowers_isPGroup_two_of_pow x k hx) (zpowers_isPGroup_two_of_pow y l hy)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro z hz
  rcases Set.mem_insert_iff.mp hz with hzx | hz
  · subst z
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  · have hz : z = y := Set.mem_singleton_iff.mp hz
    subst z
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

/-- This single interface applies to all eight literal matrix models.
Its two power equations must be supplied by whole-matrix certificates. -/
theorem matrix_model_goodSylowTwo_of_binary_powers
    (hodd : OddOrderSolvability) (p n : ℕ) (a b : Array String)
    [Finite (CFSG.Models.MatrixData.Model p n a b)]
    (hn : ¬IsMulCommutative (CFSG.Models.MatrixData.Model p n a b))
    (k l : ℕ)
    (ha : CFSG.Models.MatrixData.matrix p n a ^ (2 ^ k) = 1)
    (hb : CFSG.Models.MatrixData.matrix p n b ^ (2 ^ l) = 1) :
    GoodSylowPrime (CFSG.Models.MatrixData.Model p n a b) 2 := by
  obtain ⟨x, hx, y, hy, hxa, hyb, hgen⟩ :=
    NoncommutativeTwoFibreGenerators.matrix_model_generators p n a b hn
  let C := Subgroup.closure (CFSG.Models.MatrixData.generators p n a b)
  let xm : C := ⟨x, Subgroup.subset_closure hx⟩
  let ym : C := ⟨y, Subgroup.subset_closure hy⟩
  have hxpow : xm ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (x : Matrix (Fin n) (Fin n) (ZMod p)) ^ (2 ^ k) = 1
    rw [hxa]
    exact ha
  have hypow : ym ^ (2 ^ l) = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (y : Matrix (Fin n) (Fin n) (ZMod p)) ^ (2 ^ l) = 1
    rw [hyb]
    exact hb
  apply goodSylowTwo_of_two_power_generators hodd xm ym k l hxpow hypow
  let H : Subgroup C := Subgroup.closure ({xm, ym} : Set C)
  have hCH : C ≤ H.map C.subtype := by
    change Subgroup.closure (CFSG.Models.MatrixData.generators p n a b) ≤ H.map C.subtype
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact ⟨xm, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
    · have hz : z = y := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨ym, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
  apply top_unique
  intro z _
  obtain ⟨w, hw, he⟩ := hCH z.property
  have he' : w = z := Subtype.ext he
  exact he' ▸ hw

theorem bray_goodSylowPrime {G : Type} [Group G] [Finite G]
    (hodd : OddOrderSolvability) (a b : G) (m k : ℕ)
    (ha : a^2=1) (hrotation : (a*(b⁻¹*a*b))^(2*m+1)=1)
    (hc : (brayElement a b m)^(2^k)=1)
    (hgen : Subgroup.closure ({a,b} : Set G)=⊤) : GoodSylowPrime G 2 := by
  let c := brayElement a b m
  have ha' : a^(2^(k+1))=1 := by
    rw [pow_succ,Nat.mul_comm (2^k) 2,pow_mul,ha,one_pow]
  have hc' : c^(2^(k+1))=1 := by
    change (brayElement a b m)^(2^(k+1))=1
    rw [pow_succ,pow_mul,hc,one_pow]
  let F : Frame (pair a c) :=
    { exponent := k+1
      power i := by
        cases i with
        | false => exact ha'
        | true => exact hc'
      commute i j := by
        cases i <;> cases j
        · exact Commute.refl _
        · exact bray_commute a b m ha hrotation
        · exact (bray_commute a b m ha hrotation).symm
        · exact Commute.refl _ }
  let U := Subgroup.closure (Set.range (pair a c))
  exact SylowTwoNormalizerOfOddOrderSolvability.goodSylowTwo_of_two_binary_subgroups hodd U (U.map (MulAut.conj b⁻¹).toMonoidHom)
    F.isPGroup (F.isPGroup.map _) (join_eq_top a b m hgen)

theorem matrix_model_goodSylowTwo_of_odd_rotation
    (hodd : OddOrderSolvability) (p n : ℕ) (a b : Array String)
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
  exact bray_goodSylowPrime hodd xm ym m k hxm2 hrotpow hbraypow hgenC

end SymmetricSubgroupAsymptotics.OddOrderSolvabilityBinaryGenerators
