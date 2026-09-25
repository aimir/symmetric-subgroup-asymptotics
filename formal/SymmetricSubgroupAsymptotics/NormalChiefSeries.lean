import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain
import Mathlib.Order.OrderIsoNat

/-! Actual finite normal chief series. The series consists of literal
normal subgroups of the original group, with existence proved from the
finite normal-subgroup poset. Every adjacent original section is minimal
normal in its original quotient ambient group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure ActualChiefSeries (R : Type) [Group R] where
  length : ℕ
  subgroup : Fin (length+1)→Subgroup R
  normal : ∀i,(subgroup i).Normal
  head : subgroup 0=⊥
  last : subgroup (Fin.last length)=⊤
  step : ∀i:Fin length,subgroup i.castSucc<subgroup i.succ
  chief : ∀i:Fin length,∀K:Subgroup R,K.Normal →
    subgroup i.castSucc≤K → K≤ subgroup i.succ →
    K=subgroup i.castSucc ∨ K=subgroup i.succ

instance actualChiefSeries_normal {R:Type} [Group R] (s:ActualChiefSeries R)
    (i:Fin (s.length+1)) : (s.subgroup i).Normal := s.normal i

/-- Existence uses only finiteness of the original group. -/
theorem actualChiefSeries_nonempty (R:Type) [Group R] [Finite R] :
    Nonempty (ActualChiefSeries R) := by
  classical
  let P := {L:Subgroup R // L.Normal}
  let B : P := ⟨⊥,inferInstance⟩
  let T : P := ⟨⊤,inferInstance⟩
  obtain ⟨f,h0,n,hn,hstep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (show B≤T from (bot_le : (⊥:Subgroup R)≤⊤))
  refine ⟨{ length := n
            subgroup := fun i=>(f i).val
            normal := fun i=>(f i).property
            head := congrArg Subtype.val h0
            last := congrArg Subtype.val hn
            step := fun i=>(hstep i i.2).1
            chief := ?_ }⟩
  intro i K hK hlo hhi
  by_cases hKB : K=(f i.val).val
  · exact Or.inl hKB
  · right
    by_contra hKL
    have hlo' : f i.val<(⟨K,hK⟩:P) :=
      lt_of_le_of_ne hlo (fun he=>hKB (congrArg Subtype.val he).symm)
    have hhi' : (⟨K,hK⟩:P)<f (i.val+1) :=
      lt_of_le_of_ne hhi (fun he=>hKL (congrArg Subtype.val he))
    exact (hstep i i.2).2 hlo' hhi'

noncomputable def actualChiefSeries (R:Type) [Group R] [Finite R] : ActualChiefSeries R :=
  Classical.choice (actualChiefSeries_nonempty R)

section Factor
variable {R:Type} [Group R] (B L:Subgroup R) [B.Normal] [L.Normal]
variable (hBL:B≤L)
variable (hc:∀K:Subgroup R,K.Normal → B≤K → K≤L → K=B ∨ K=L)
include hBL hc

theorem normalChiefFactor_minimal :
    ∀K:Subgroup (R⧸B),K.Normal → K≤normalChainQuotient B L →
      K=⊥ ∨ K=normalChainQuotient B L := by
  intro K hK hKL
  let π := QuotientGroup.mk' B
  have hlo : B≤K.comap π := by
    intro x hx
    change π x∈K
    have he : π x=1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [he]
    exact K.one_mem
  have hhi : K.comap π≤L := by
    calc
      K.comap π≤(L.map π).comap π := Subgroup.comap_mono hKL
      _=L := Subgroup.comap_map_eq_self (by simpa only [π,QuotientGroup.ker_mk'] using hBL)
  rcases hc (K.comap π) (hK.comap π) hlo hhi with he|he
  · left
    have h := congrArg (Subgroup.map π) he
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective B)] at h
    exact h.trans ((Subgroup.map_eq_bot_iff B).mpr (by simp [π]))
  · right
    have h := congrArg (Subgroup.map π) he
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective B)] at h
    exact h

end Factor

end SymmetricSubgroupAsymptotics
