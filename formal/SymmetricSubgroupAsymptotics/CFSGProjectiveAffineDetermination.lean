import SymmetricSubgroupAsymptotics.CFSGProjectiveAffineDiagonal

/-! The original affine chart determines a coordinate-point-fixing
projective collineation, including every point at infinity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
open CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

private theorem infinity_line_submodule_le (v : n→F) (p : Point (F:=F) (n:=n))
    (hp : p∈(infinity (F:=F) (n:=n)).projectivization)
    (hline : OnLine p (point (0 : n→F)) (point v)) :
    p.submodule≤F ∙ (vector v-vector (0 : n→F)) := by
  have hm := hline (show p.rep∈p.submodule from
    by rw [Projectivization.submodule_eq];exact Submodule.mem_span_singleton_self p.rep)
  change p.rep∈(F ∙ vector (0 : n→F)) ⊔ (F ∙ vector v) at hm
  obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp hm
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have h0 := congrArg (fun x : Vector (F:=F) (n:=n) => x (Sum.inl ())) he
  have hp0 := (mem_projective_infinity p).mp hp
  have hab : a+b=0 := by
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,vector_zeroCoord,mul_one,hp0] using h0
  have ha : a=-b := eq_neg_of_add_eq_zero_left hab
  rw [Projectivization.submodule_eq,Submodule.span_singleton_le_iff_mem]
  apply Submodule.mem_span_singleton.mpr
  refine ⟨b,?_⟩
  calc
    b • (vector v-vector (0 : n→F))=a • vector (0 : n→F)+b • vector v := by
      rw [ha]
      funext k
      simp only [Pi.smul_apply,Pi.sub_apply,Pi.add_apply,smul_eq_mul]
      ring
    _=p.rep := he

private theorem infinity_onLine_unique (v : n→F) (p q : Point (F:=F) (n:=n))
    (hp : p∈(infinity (F:=F) (n:=n)).projectivization)
    (hq : q∈(infinity (F:=F) (n:=n)).projectivization)
    (hpl : OnLine p (point (0 : n→F)) (point v))
    (hql : OnLine q (point (0 : n→F)) (point v)) : p=q := by
  have hP := infinity_line_submodule_le v p hp hpl
  have hQ := infinity_line_submodule_le v q hq hql
  have hd : vector v-vector (0 : n→F)≠0 := by
    intro he
    have hb : p.submodule≤⊥ := by simpa only [he,Submodule.span_zero_singleton] using hP
    have hc := Submodule.finrank_mono hb
    rw [Projectivization.finrank_submodule,finrank_bot] at hc
    exact Nat.not_succ_le_zero 0 hc
  have hdim := finrank_span_singleton (K:=F) hd
  have heP : p.submodule=F ∙ (vector v-vector (0 : n→F)) :=
    Submodule.eq_of_le_of_finrank_eq hP (by rw [Projectivization.finrank_submodule,hdim])
  have heQ : q.submodule=F ∙ (vector v-vector (0 : n→F)) :=
    Submodule.eq_of_le_of_finrank_eq hQ (by rw [Projectivization.finrank_submodule,hdim])
  exact Projectivization.submodule_injective (heP.trans heQ.symm)

private theorem infinity_onLine_coordinates (p : Point (F:=F) (n:=n))
    (hp : p∈(infinity (F:=F) (n:=n)).projectivization) :
    OnLine p (point (0 : n→F)) (point (fun i => p.rep (Sum.inr i))) := by
  let v : n→F := fun i => p.rep (Sum.inr i)
  have hp0 := (mem_projective_infinity p).mp hp
  have he : p.rep=vector v-vector (0 : n→F) := by
    funext k
    rcases k with u | k
    · cases u
      simp only [Pi.sub_apply,vector_zeroCoord,sub_self,hp0]
    · simp only [Pi.sub_apply,vector_coord,Pi.zero_apply,sub_zero,v]
  change p.submodule≤(point (0 : n→F)).submodule ⊔ (point v).submodule
  rw [show p.submodule=F ∙ p.rep from Projectivization.submodule_eq p]
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  rw [he]
  exact Submodule.sub_mem _
    ((show (F ∙ vector v)≤(point (0 : n→F)).submodule ⊔ (point v).submodule from le_sup_right)
      (Submodule.mem_span_singleton_self _))
    ((show (F ∙ vector (0 : n→F))≤(point (0 : n→F)).submodule ⊔ (point v).submodule from le_sup_left)
      (Submodule.mem_span_singleton_self _))

theorem collineation_ext_of_affine
    (f g : collineationGroup (F:=F) (n:=Unit⊕n))
    (hf : ∀i : Unit⊕n,f.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (hg : ∀i : Unit⊕n,g.val (basisPoint (F:=F) i)=basisPoint (F:=F) i)
    (haff : affinePermutation f hf=affinePermutation g hg) : f=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p∈(infinity (F:=F) (n:=n)).projectivization
  · let v : n→F := fun i => p.rep (Sum.inr i)
    have hline := infinity_onLine_coordinates p hp
    change OnLine p (point (0 : n→F)) (point v) at hline
    have hfp := (mem_coordinateHyperplane_image_iff f hf (Sum.inl ()) p).mpr hp
    have hgp := (mem_coordinateHyperplane_image_iff g hg (Sum.inl ()) p).mpr hp
    have hf0 : f.val (point (0 : n→F))=point 0 := by rw [point_zero,hf]
    have hg0 : g.val (point (0 : n→F))=point 0 := by rw [point_zero,hg]
    have hfline : OnLine (f.val p) (point (0 : n→F)) (point (affinePermutation f hf v)) := by
      simpa only [hf0,←point_affinePermutation f hf v] using (f.property _ _ _).mpr hline
    have hgline : OnLine (g.val p) (point (0 : n→F)) (point (affinePermutation f hf v)) := by
      simpa only [hg0,←point_affinePermutation g hg v,←haff] using (g.property _ _ _).mpr hline
    exact infinity_onLine_unique _ _ _ hfp hgp hfline hgline
  · have he := point_coordinates p hp
    calc
      f.val p=f.val (point (coordinates p)) := congrArg f.val he.symm
      _=point (affinePermutation f hf (coordinates p)) := (point_affinePermutation f hf _).symm
      _=point (affinePermutation g hg (coordinates p)) :=
        congrArg (fun e : Equiv.Perm (n→F) => point (e (coordinates p))) haff
      _=g.val (point (coordinates p)) := point_affinePermutation g hg _
      _=g.val p := congrArg g.val he

end SymmetricSubgroupAsymptotics.CFSGProjectiveAffineChart
