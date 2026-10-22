import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! A triangle of singular planes has a common point unless their
span is singular. The proof uses their actual submodule intersections,
not an abstract polar-space or building theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

def ZeroOn (B : LinearMap.BilinForm K V) (P Q : Submodule K V) : Prop :=
  ∀ x∈P,∀y∈Q,B x y=0

private theorem join_lines (N A P : Submodule K V)
    (hN : Module.finrank K N=1) (hA : Module.finrank K A=1)
    (hP : Module.finrank K P=2) (hNA : N⊓A=⊥) (hNP : N≤P) (hAP : A≤P) :
    N⊔A=P := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq N A
  rw [hNA,finrank_bot,hN,hA] at hdim
  apply Submodule.eq_of_le_of_finrank_le (sup_le hNP hAP)
  omega

theorem orthogonal_of_no_common_point (B : LinearMap.BilinForm K V)
    (P Q R : Submodule K V)
    (hP : Module.finrank K P=2) (hQ : Module.finrank K Q=2)
    (hPQ : Module.finrank K (P⊓Q : Submodule K V)=1)
    (hPR : Module.finrank K (P⊓R : Submodule K V)=1)
    (hQR : Module.finrank K (Q⊓R : Submodule K V)=1)
    (zP : ZeroOn B P P) (zQ : ZeroOn B Q Q) (zR : ZeroOn B R R)
    (hn : ¬P⊓Q≤R) : ZeroOn B P Q := by
  let N : Submodule K V := P⊓Q
  let A : Submodule K V := P⊓R
  let C : Submodule K V := Q⊓R
  have hNZ : N⊓R=⊥ := by
    by_contra hne
    have hpos : 0 < Module.finrank K (N⊓R : Submodule K V) :=
      Nat.pos_of_ne_zero (fun h=>hne (Submodule.finrank_eq_zero.mp h))
    have he : N⊓R=N := Submodule.eq_of_le_of_finrank_le inf_le_left (by
      change Module.finrank K (P⊓Q : Submodule K V) ≤ _
      rw [hPQ]
      omega)
    exact hn (he.ge.trans inf_le_right)
  have hNA : N⊓A=⊥ := by
    change (P⊓Q)⊓(P⊓R)=⊥
    simpa only [N,inf_assoc,inf_left_comm,inf_left_idem] using hNZ
  have hNC : N⊓C=⊥ := by
    change (P⊓Q)⊓(Q⊓R)=⊥
    simpa only [N,inf_assoc,inf_left_comm,inf_left_idem] using hNZ
  have heP : N⊔A=P := join_lines N A P hPQ hPR hP hNA inf_le_left inf_le_left
  have heQ : N⊔C=Q := join_lines N C Q hPQ hQR hQ hNC inf_le_right inf_le_left
  intro x hx y hy
  rw [←heP] at hx
  rw [←heQ] at hy
  obtain ⟨u,hu,a,ha,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨v,hv,c,hc,rfl⟩ := Submodule.mem_sup.mp hy
  have huv : B u v=0 := zP u hu.1 v hv.1
  have huc : B u c=0 := zQ u hu.2 c hc.1
  have hav : B a v=0 := zP a ha.1 v hv.1
  have hac : B a c=0 := zR a ha.2 c hc.2
  simp only [map_add,LinearMap.add_apply,huv,huc,hav,hac,add_zero]

theorem common_point_of_nonorthogonal (B : LinearMap.BilinForm K V)
    (P Q R : Submodule K V)
    (hP : Module.finrank K P=2) (hQ : Module.finrank K Q=2)
    (hPQ : Module.finrank K (P⊓Q : Submodule K V)=1)
    (hPR : Module.finrank K (P⊓R : Submodule K V)=1)
    (hQR : Module.finrank K (Q⊓R : Submodule K V)=1)
    (zP : ZeroOn B P P) (zQ : ZeroOn B Q Q) (zR : ZeroOn B R R)
    (hn : ¬ZeroOn B P Q) : P⊓Q≤R := by
  by_contra hnot
  exact hn (orthogonal_of_no_common_point B P Q R hP hQ hPQ hPR hQR zP zQ zR hnot)

end SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
