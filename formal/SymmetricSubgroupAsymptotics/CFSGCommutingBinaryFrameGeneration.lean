import SymmetricSubgroupAsymptotics.CFSGSylowTwoNormalizerSolvable
import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-! Two actual commuting binary frames, together with literal recovery
words for the original generating tuple, certify Good Sylow two.
Frames may be elementary abelian, cyclic or degenerate; no order-four
element, subgroup order, maximality or independent generation label is
assumed. The whole-element power and recovery equations are proof data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCommutingBinaryFrameGeneration

variable {G H ι κ τ : Type*} [Group G] [Group H]

structure Frame (seed : ι → G) where
  exponent : ℕ
  power : ∀ i,seed i^(2^exponent)=1
  commute : ∀ i j,Commute (seed i) (seed j)

theorem Frame.isPGroup {seed : ι → G} (F : Frame seed) :
    IsPGroup 2 (Subgroup.closure (Set.range seed)) := by
  have habel : IsMulCommutative (Subgroup.closure (Set.range seed)) := by
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact (F.commute i j).eq
  have hpow : ∀ x (hx : x∈Subgroup.closure (Set.range seed)),x^(2^F.exponent)=1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i,rfl⟩ := hx
        exact F.power i
    | one => simp only [one_pow]
    | mul x y hx hy hpx hpy =>
        have hxy : Commute x y :=
          congrArg Subtype.val (habel.is_comm.comm
            (⟨x,hx⟩ : Subgroup.closure (Set.range seed)) ⟨y,hy⟩)
        rw [hxy.mul_pow,hpx,hpy,one_mul]
    | inv x hx hp => rw [inv_pow,hp,inv_one]
  intro x
  refine ⟨F.exponent,Subtype.ext ?_⟩
  exact hpow x.val x.property

def Frame.map {seed : ι → G} (F : Frame seed) (f : G →* H) :
    Frame (fun i => f (seed i)) where
  exponent := F.exponent
  power i := by rw [←map_pow,F.power i,map_one]
  commute i j := by
    change f (seed i)*f (seed j)=f (seed j)*f (seed i)
    rw [←map_mul,←map_mul,(F.commute i j).eq]

theorem combined_closure_le_join (u : ι → G) (v : τ → G) :
    Subgroup.closure (Set.range (Sum.elim u v))≤
      Subgroup.closure (Set.range u)⊔Subgroup.closure (Set.range v) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  cases j with
  | inl i => exact Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_range_self i))
  | inr i => exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_range_self i))

theorem join_eq_top_of_recovery (original : κ → G)
    (hgen : Subgroup.closure (Set.range original)=⊤) (u : ι → G) (v : τ → G)
    (C : FiniteGeneratorWordCertificate original (Sum.elim u v)) :
    Subgroup.closure (Set.range u)⊔Subgroup.closure (Set.range v)=⊤ := by
  apply top_unique
  rw [←hgen]
  exact C.closure_le.trans (combined_closure_le_join u v)

theorem goodSylowTwo_of_recovery {G : Type} [Group G] [Finite G]
    (hCFSG : CFSG.CFSGClassification) {ι κ τ : Type}
    (original : κ → G) (hgen : Subgroup.closure (Set.range original)=⊤)
    (u : ι → G) (v : τ → G) (Fu : Frame u) (Fv : Frame v)
    (C : FiniteGeneratorWordCertificate original (Sum.elim u v)) :
    CFSGReduction.GoodSylowPrime G 2 := by
  exact CFSGReduction.goodSylowTwo_of_two_binary_subgroups hCFSG
    (Subgroup.closure (Set.range u)) (Subgroup.closure (Set.range v))
    Fu.isPGroup Fv.isPGroup (join_eq_top_of_recovery original hgen u v C)

def pair (a z : G) : Bool → G
  | false => a
  | true => z

def pairFrame (a z : G) (ha : a^2=1) (hz : z^2=1) (haz : Commute a z) :
    Frame (pair a z) where
  exponent := 1
  power i := by
    cases i with
    | false => simpa only [pair,pow_one] using ha
    | true => simpa only [pair,pow_one] using hz
  commute i j := by
    cases i <;> cases j
    · exact Commute.refl a
    · exact haz
    · exact haz.symm
    · exact Commute.refl z

/-- The dihedral half-turn is a commuting binary seed from an actual
whole-element equation. No exact order or nontriviality is needed. -/
theorem half_product_properties (a t : G) (ha : a^2=1) (ht : t^2=1)
    (m : ℕ) (hrotation : (a*t)^(2*m)=1) :
    ((a*t)^m)^2=1 ∧ Commute a ((a*t)^m) := by
  have haa : a*a=1 := by simpa only [pow_two] using ha
  have htt : t*t=1 := by simpa only [pow_two] using ht
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_right haa
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_right htt
  have hconj : a*(a*t)*a⁻¹=(a*t)⁻¹ := by
    calc
      a*(a*t)*a⁻¹=((a*a)*t)*a := by rw [hai]; group
      _=t*a := by rw [haa,one_mul]
      _=(a*t)⁻¹ := by rw [mul_inv_rev,hai,hti]
  have hz : ((a*t)^m)^2=1 := by
    rw [←pow_mul,Nat.mul_comm m 2]
    exact hrotation
  have hzi : ((a*t)^m)⁻¹=(a*t)^m :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz)
  have hp := map_pow (MulAut.conj a).toMonoidHom (a*t) m
  change a*((a*t)^m)*a⁻¹=(a*(a*t)*a⁻¹)^m at hp
  rw [hconj,inv_pow] at hp
  refine ⟨hz,?_⟩
  change a*(a*t)^m=(a*t)^m*a
  calc
    a*(a*t)^m=(a*((a*t)^m)*a⁻¹)*a := by group
    _=(a*t)^m*a := by rw [hp,hzi]

def halfProductFrame (a t : G) (ha : a^2=1) (ht : t^2=1)
    (m : ℕ) (hrotation : (a*t)^(2*m)=1) : Frame (pair a ((a*t)^m)) :=
  pairFrame a ((a*t)^m) ha (half_product_properties a t ha ht m hrotation).1
    (half_product_properties a t ha ht m hrotation).2

end SymmetricSubgroupAsymptotics.CFSGCommutingBinaryFrameGeneration
