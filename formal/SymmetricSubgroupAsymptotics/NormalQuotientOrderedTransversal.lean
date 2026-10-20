import SymmetricSubgroupAsymptotics.PGroupOrderedTransversal

/-! Compose an actual kernel transversal with an actual quotient
transversal. The lower representatives lie in the kernel; this is the
normal-series step for soluble ordered transversals, and does not assume
the original point stabilizer is subnormal. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {G Q I J : Type*} [Group G] [Group Q]

/-- The higher quotient coordinate is the most significant coordinate. -/
def normalQuotientGridLT (ltI : I → I → Prop) (ltJ : J → J → Prop)
    (a b : I×J) : Prop := ltI a.1 b.1 ∨ a.1=b.1 ∧ ltJ a.2 b.2

def normalQuotientGridComparable (rI : I → I → Prop) (rJ : J → J → Prop)
    (a b : I×J) : Prop := rI a.1 b.1 ∧ rJ a.2 b.2

private theorem mem_of_image_mem (q : G →* Q) (K : Subgroup G)
    (hker : q.ker≤K) {y : G} (hy : q y∈K.map q) : y∈K := by
  obtain ⟨k,hk,hqk⟩ := hy
  have he : y*k⁻¹∈q.ker := by
    change q (y*k⁻¹)=1
    rw [map_mul,map_inv,hqk,mul_inv_cancel]
  have h := K.mul_mem (hker he) hk
  simpa only [inv_mul_cancel_right] using h

/-- The actual right transversal obtained by composing lower-kernel and
upper-quotient coordinates. Every factorization and the full triangular
transport are proved on the original ambient group. -/
theorem orderedTransversal_of_normalQuotient
    (q : G →* Q) (hq : Function.Surjective q)
    (H K : Subgroup G) (hker : q.ker≤K)
    (ltI rI : I → I → Prop) (ltJ rJ : J → J → Prop)
    (D : OrderedCosetData H K J ltJ rJ)
    (hDker : ∀ j, D.repr j∈q.ker)
    (E : OrderedCosetData (K.map q) ⊤ I ltI rI) :
    Nonempty (OrderedCosetData H ⊤ (I×J)
      (normalQuotientGridLT ltI ltJ) (normalQuotientGridComparable rI rJ)) := by
  let U : I → G := fun i => (hq (E.repr i)).choose
  have hU : ∀ i, q (U i)=E.repr i := fun i => (hq (E.repr i)).choose_spec
  let T : I×J → G := fun a => D.repr a.2*U a.1
  have hqT : ∀ a, q (T a)=E.repr a.1 := by
    intro a
    have hd : q (D.repr a.2)=1 := hDker a.2
    simp only [T,map_mul,hd,one_mul,hU]
  have hlift (y : G) (i : I) (h : Q) (hh : h∈K.map q)
      (hy : q y=h*E.repr i) :
      ∃ k : G, k∈K ∧ y=k*U i := by
    let k := y*(U i)⁻¹
    have hk : k∈K := mem_of_image_mem q K hker (by
      change q (y*(U i)⁻¹)∈K.map q
      simpa only [map_mul,map_inv,hU,hy,mul_inv_cancel_right] using hh)
    exact ⟨k,hk,by dsimp [k]; group⟩
  refine ⟨{ le := le_top
            repr := T
            mem := fun _ => Subgroup.mem_top _
            factor := ?_
            unique := ?_
            triangular := ?_ }⟩
  · intro y _
    obtain ⟨h,hh,i,hy⟩ := E.factor (q y) (Subgroup.mem_top _)
    obtain ⟨k,hk,hki⟩ := hlift y i h hh hy
    obtain ⟨h',hh',j,hkj⟩ := D.factor k hk
    exact ⟨h',hh',(i,j),by rw [hki,hkj]; simp only [T,mul_assoc]⟩
  · intro a b hab
    have hup : a.1=b.1 := E.unique a.1 b.1 (by
      have hm := Subgroup.mem_map_of_mem q (D.le hab)
      simpa only [map_mul,map_inv,hqT] using hm)
    have hlo : a.2=b.2 := D.unique a.2 b.2 (by
      simpa only [T,hup,mul_inv_rev,mul_assoc,mul_inv_cancel_left,mul_one] using hab)
    exact Prod.ext hup hlo
  · intro a b c hab hbc
    rcases hbc with ⟨hbcI,hbcJ⟩
    rcases hab with habI|⟨habI,habJ⟩
    · obtain ⟨h,hh,e,hec,he⟩ := E.triangular a.1 b.1 c.1 habI hbcI
      obtain ⟨k,hk,hky⟩ := hlift (T a*(T b)⁻¹*T c) e h hh (by
        simpa only [map_mul,map_inv,hqT] using he)
      obtain ⟨h',hh',j,hkj⟩ := D.factor k hk
      refine ⟨h',hh',(e,j),Or.inl hec,?_⟩
      rw [hky,hkj]
      simp only [T,mul_assoc]
    · obtain ⟨h,hh,j,hjc,hj⟩ := D.triangular a.2 b.2 c.2 habJ hbcJ
      refine ⟨h,hh,(c.1,j),Or.inr ⟨rfl,hjc⟩,?_⟩
      change (D.repr a.2*U a.1)*(D.repr b.2*U b.1)⁻¹*
        (D.repr c.2*U c.1)=h*(D.repr j*U c.1)
      rw [habI]
      calc
        _ = (D.repr a.2*(D.repr b.2)⁻¹*D.repr c.2)*U c.1 := by group
        _ = _ := by rw [hj,mul_assoc]

end SymmetricSubgroupAsymptotics
