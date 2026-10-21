import SymmetricSubgroupAsymptotics.CFSGTypeAColumnFormCoordinates
import SymmetricSubgroupAsymptotics.CFSGTypeAPointRootCardinality
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! All nonidentity members of the actual fixed-centre root group are
conjugate in PSL when the complementary dimension is at least two.
The conjugators are literal determinant-one block matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAColumnRootConjugacy
open Matrix CFSGTypeAProjectivePointRoots CFSGTypeABlockEmbedding
open CFSGTypeAColumnFormCoordinates
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem exists_form_conjugator (b c : n) (hbc : b≠c)
    (f g : pointForms (firstVector (F:=F) (n:=n))) (hf : f≠0) (hg : g≠0) :
    ∃ A : BigSL (F:=F) (n:=n),
      A*transvectionSL f.property*A⁻¹=transvectionSL g.property := by
  obtain ⟨B,hB⟩ := CFSGTypeAVectorTransitivity.exists_map_nonzero b c hbc
    (coefficients f) (coefficients g) (coefficients_ne_zero hf) (coefficients_ne_zero hg)
  change B.val *ᵥ coefficients f=coefficients g at hB
  let C : Matrix.SpecialLinearGroup n F := (Matrix.SpecialLinearGroup.transpose B)⁻¹
  let A : BigSL (F:=F) (n:=n) := blockHom C
  have hCt : (C⁻¹).val=B.val.transpose := by
    simp only [C,inv_inv,Matrix.SpecialLinearGroup.coe_transpose]
  have hform (x : Unit ⊕ n→F) : f.val (A.toLin'.symm x)=g.val x := by
    rw [show A=blockHom C from rfl,form_comp_block_inverse]
    rw [Matrix.SpecialLinearGroup.toLin'_apply,hCt,Matrix.toLin'_apply,
      Matrix.dotProduct_transpose_mulVec,hB,dotProduct_comm,←form_apply]
  refine ⟨A,?_⟩
  apply Matrix.SpecialLinearGroup.toLin'_injective
  rw [map_mul,map_mul,map_inv]
  apply LinearEquiv.ext
  intro x
  simp only [LinearEquiv.mul_apply,LinearEquiv.coe_inv]
  rw [transvectionSL_apply,map_add,map_smul,LinearEquiv.apply_symm_apply]
  rw [show A.toLin' (firstVector (F:=F) (n:=n))=firstVector from blockHom_firstVector C,
    hform,transvectionSL_apply]

theorem nonidentity_conjugate (b c : n) (hbc : b≠c)
    (a d : pointRoot (firstVector (F:=F) (n:=n))) (ha : a≠1) (hd : d≠1) :
    ∃ z : PSL (F:=F) (n:=Unit ⊕ n), z*(a : PSL (F:=F) (n:=Unit ⊕ n))*z⁻¹=d := by
  obtain ⟨f,hf⟩ := a.property
  obtain ⟨g,hg⟩ := d.property
  have hf0 : f.toAdd≠0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [←hf,show f=1 from congrArg Multiplicative.ofAdd he,map_one]
    rfl
  have hg0 : g.toAdd≠0 := by
    intro he
    apply hd
    apply Subtype.ext
    rw [←hg,show g=1 from congrArg Multiplicative.ofAdd he,map_one]
    rfl
  obtain ⟨A,hA⟩ := exists_form_conjugator b c hbc f.toAdd g.toAdd hf0 hg0
  refine ⟨projection A,?_⟩
  rw [←hf,←hg]
  change projection A*projection (transvectionSL f.toAdd.property)*(projection A)⁻¹=
    projection (transvectionSL g.toAdd.property)
  rw [←map_inv,←map_mul,←map_mul,hA]

theorem field_power_le_proper_index [Finite F]
    [IsSimpleGroup (PSL (F:=F) (n:=Unit ⊕ n))]
    (b c : n) (hbc : b≠c) (H : Subgroup (PSL (F:=F) (n:=Unit ⊕ n))) (hH : H≠⊤) :
    Nat.card F^Fintype.card n≤H.index := by
  have hv : (firstVector (F:=F) (n:=n))≠0 := by
    intro he
    have hh := congrArg (fun v : Unit ⊕ n→F => v (Sum.inl ())) he
    simpa only [firstVector,Pi.single_eq_same,Pi.zero_apply,one_ne_zero] using hh
  let f : pointForms (firstVector (F:=F) (n:=n)) :=
    ⟨(LinearMap.proj (Sum.inr b) : ((Unit ⊕ n)→F)→ₗ[F]F),by
      change (firstVector (F:=F) (n:=n)) (Sum.inr b)=0
      simp [firstVector,Pi.single_apply]⟩
  have hf : f≠0 := by
    intro he
    have hh := congrArg (fun t : pointForms (firstVector (F:=F) (n:=n)) =>
      t.val (Pi.single (Sum.inr b) 1)) he
    simpa [f] using hh
  let a : pointRoot (firstVector (F:=F) (n:=n)) :=
    ⟨pointRootHom firstVector (Multiplicative.ofAdd f),⟨_,rfl⟩⟩
  have ha : a≠1 := by
    intro he
    have hh : pointRootHom firstVector (Multiplicative.ofAdd f)=
        pointRootHom firstVector 1 := by
      exact (congrArg (fun z : pointRoot (firstVector (F:=F) (n:=n)) =>
        (z : PSL (F:=F) (n:=Unit ⊕ n))) he).trans (map_one (pointRootHom firstVector)).symm
    have hparam := pointRootHom_injective hv hh
    exact hf (congrArg Multiplicative.toAdd hparam)
  letI : Nontrivial (pointRoot (firstVector (F:=F) (n:=n))) := ⟨⟨a,1,ha⟩⟩
  have hbound := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate
    (pointRoot (firstVector (F:=F) (n:=n))) (nonidentity_conjugate b c hbc) H hH
  have hcard : Nat.card (pointRoot (firstVector (F:=F) (n:=n)))=
      Nat.card F^Fintype.card n := by
    rw [pointRoot_card hv,Fintype.card_sum,Fintype.card_unit]
    congr 1
    omega
  rw [hcard] at hbound
  exact hbound

end SymmetricSubgroupAsymptotics.CFSGTypeAColumnRootConjugacy
