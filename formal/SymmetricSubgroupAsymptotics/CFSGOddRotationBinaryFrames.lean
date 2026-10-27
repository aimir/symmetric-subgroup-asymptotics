import SymmetricSubgroupAsymptotics.CFSGCommutingBinaryFrameGeneration

/-! A whole odd rotation gives a Bray centralizer element. If that SAME
element has certified binary power, two commuting binary frames generate
the original group. Original generator recovery is an algebraic identity,
not a search, model recognition or normal-generation assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOddRotationBinaryFrames
open CFSGCommutingBinaryFrameGeneration CFSGReduction

variable {G : Type*} [Group G]

def brayElement (a b : G) (m : ℕ) : G :=
  (a*(b⁻¹*a*b))^(m+1)*b⁻¹

/-- Right-conjugation convention a^b=b^-1*a*b. The exponent is m+1. -/
theorem bray_commute (a b : G) (m : ℕ) (ha : a^2=1)
    (hrotation : (a*(b⁻¹*a*b))^(2*m+1)=1) : Commute a (brayElement a b m) := by
  let r := a*(b⁻¹*a*b)
  let t := r^(m+1)
  have haa : a*a=1 := by simpa only [pow_two] using ha
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right haa
  have hqa : b⁻¹*a*b=a*r := by
    dsimp only [r]
    calc
      _=1*(b⁻¹*a*b) := (one_mul _).symm
      _=(a*a)*(b⁻¹*a*b) := by rw [haa]
      _=a*(a*(b⁻¹*a*b)) := mul_assoc _ _ _
  have hinvert : a*r*a⁻¹=r⁻¹ := by
    dsimp only [r]
    calc
      a*(a*(b⁻¹*a*b))*a⁻¹=(a*a)*(b⁻¹*a*b)*a⁻¹ := by group
      _=(b⁻¹*a*b)*a := by rw [haa,one_mul,hai]
      _=(a*(b⁻¹*a*b))⁻¹ := by
        rw [mul_inv_rev,mul_inv_rev,mul_inv_rev,inv_inv,hai]
        group
  have hpow := map_pow (MulAut.conj a).toMonoidHom r (m+1)
  change a*t*a⁻¹=(a*r*a⁻¹)^(m+1) at hpow
  rw [hinvert,inv_pow] at hpow
  have hta : t*a=a*t⁻¹ := by
    calc
      t*a=(a*a)*t*a := by rw [haa,one_mul]
      _=a*(a*t*a⁻¹) := by rw [hai]; group
      _=a*t⁻¹ := by rw [hpow]
  have htt : t*t=r := by
    calc
      t*t=r^((m+1)+(m+1)) := (pow_add r _ _).symm
      _=r^((2*m+1)+1) := congrArg (fun n : ℕ => r^n) (by omega)
      _=r := by rw [pow_succ,hrotation,one_mul]
  have hct : brayElement a b m*a=a*brayElement a b m := by
    change (t*b⁻¹)*a=a*(t*b⁻¹)
    calc
      (t*b⁻¹)*a=t*(b⁻¹*a*b)*b⁻¹ := by group
      _=t*(a*r)*b⁻¹ := by rw [hqa]
      _=(t*a)*r*b⁻¹ := by group
      _=(a*t⁻¹)*r*b⁻¹ := by rw [hta]
      _=a*(t⁻¹*r)*b⁻¹ := by group
      _=a*(t*b⁻¹) := by rw [←htt]; group
  exact hct.symm

/-- The recovery identity itself needs no power, finiteness or simplicity. -/
theorem join_eq_top (a b : G) (m : ℕ)
    (hgen : Subgroup.closure ({a,b} : Set G)=⊤) :
    let U := Subgroup.closure (Set.range (pair a (brayElement a b m)))
    U⊔U.map (MulAut.conj b⁻¹).toMonoidHom=⊤ := by
  let c := brayElement a b m
  let U := Subgroup.closure (Set.range (pair a c))
  let H := U⊔U.map (MulAut.conj b⁻¹).toMonoidHom
  have haU : a∈U := Subgroup.subset_closure ⟨false,rfl⟩
  have hcU : c∈U := Subgroup.subset_closure ⟨true,rfl⟩
  have haH : a∈H := Subgroup.mem_sup_left haU
  have hcH : c∈H := Subgroup.mem_sup_left hcU
  have habH : b⁻¹*a*b∈H := by
    apply Subgroup.mem_sup_right
    exact ⟨a,haU,by change b⁻¹*a*(b⁻¹)⁻¹=b⁻¹*a*b; rw [inv_inv]⟩
  have htH : (a*(b⁻¹*a*b))^(m+1)∈H := H.pow_mem (H.mul_mem haH habH) _
  have hbiH : b⁻¹∈H := by
    have hh := H.mul_mem (H.inv_mem htH) hcH
    have he : ((a*(b⁻¹*a*b))^(m+1))⁻¹*c=b⁻¹ := by
      dsimp only [c,brayElement]
      group
    exact he ▸ hh
  have hbH : b∈H := by simpa only [inv_inv] using H.inv_mem hbiH
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact haH
  · have he : x=b := Set.mem_singleton_iff.mp hx
    subst x
    exact hbH

/-- The binary-power equation is a whole-element certificate premise.
No particular model is claimed to satisfy it by this generic theorem. -/
theorem goodSylowPrime {G : Type} [Group G] [Finite G]
    (hCFSG : CFSG.CFSGClassification) (a b : G) (m k : ℕ)
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
  exact goodSylowTwo_of_two_binary_subgroups hCFSG U (U.map (MulAut.conj b⁻¹).toMonoidHom)
    F.isPGroup (F.isPGroup.map _) (join_eq_top a b m hgen)

end SymmetricSubgroupAsymptotics.CFSGOddRotationBinaryFrames
