import SymmetricSubgroupAsymptotics.PrimitiveSoclePointStabilizerCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveSocleInvariantColor
import SymmetricSubgroupAsymptotics.PrimitiveStabilizerInvariantInterval

/-! The exact two degree forms for an actual homogeneous minimal normal
subgroup of a faithful primitive action. The original point stabilizer is
used throughout; diagonal correlations are never discarded. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

theorem mem_pointStabilizerCoordinates
    {E X T : Type} [Group E] [Group T] [MulAction E X]
    (k : ℕ) (e : E ≃* (Fin k → T)) (x : X) (z : Fin k → T) :
    z∈pointStabilizerCoordinates k e x ↔ e.symm z • x=x := by
  constructor
  · rintro ⟨u,hu,he⟩
    change e u=z at he
    have hu' : e.symm z=u := by rw [←he,e.symm_apply_apply]
    simpa only [hu'] using hu
  · intro hz
    exact ⟨e.symm z,hz,e.apply_symm_apply z⟩

theorem coordinateConjugation_preserves_stabilizer
    {G X T : Type} [Group G] [Group T] [MulAction G X]
    (E : Subgroup G) [E.Normal] (k : ℕ) (e : E ≃* (Fin k → T))
    (x : X) (p : G) (hp : p∈MulAction.stabilizer G x) :
    ∀ z, coordinateConjugation E k e p z∈pointStabilizerCoordinates k e x ↔
      z∈pointStabilizerCoordinates k e x := by
  intro z
  rw [mem_pointStabilizerCoordinates,mem_pointStabilizerCoordinates]
  have he : e.symm (coordinateConjugation E k e p z)=
      MulAut.conjNormal p (e.symm z) := e.symm_apply_apply _
  rw [he]
  have hp' : p • x=x := hp
  have hpi : p⁻¹ • x=x := (MulAction.stabilizer G x).inv_mem hp
  change (p*(e.symm z : G)*p⁻¹) • x=x ↔ (e.symm z : G) • x=x
  rw [mul_smul,mul_smul,hpi]
  constructor
  · intro h
    have hh := congrArg (fun y : X => p⁻¹ • y) h
    simpa only [inv_smul_smul,hpi] using hh
  · intro h
    rw [h,hp']

/-- Maximality of the actual point stabilizer forces a proper coordinate
projection product to coincide with that same original stabilizer. -/
theorem proper_projectionClosure_eq_stabilizer
    {G X T : Type} [Group G] [Group T] [Finite T] [IsSimpleGroup T]
    [MulAction G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (E : Subgroup G) [E.Normal] (hT : IsCenterless T)
    (k : ℕ) (e : E ≃* (Fin k → T)) (x : X)
    (hproper : projectionClosure (pointStabilizerCoordinates k e x)≠⊤) :
    projectionClosure (pointStabilizerCoordinates k e x)=pointStabilizerCoordinates k e x := by
  let K := pointStabilizerCoordinates k e x
  let L : Subgroup E := (projectionClosure K).comap e.toMonoidHom
  let C : Subgroup G := L.map E.subtype
  have hCE : C≤E := by rintro g ⟨u,_,rfl⟩; exact u.property
  have hcap : E⊓MulAction.stabilizer G x≤C := by
    intro g hg
    let u : E := ⟨g,hg.1⟩
    refine ⟨u,?_,rfl⟩
    apply le_projectionClosure K
    exact ⟨u,hg.2,rfl⟩
  have hnorm : MulAction.stabilizer G x≤Subgroup.normalizer C := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro p hp g ⟨u,hu,rfl⟩
    refine ⟨MulAut.conjNormal p u,?_,rfl⟩
    have hK := coordinateConjugation_preserves_stabilizer E k e x p hp
    have h := projectionClosure_automorphism hT K
      (coordinateConjugation E k e p) hK hu
    change e (MulAut.conjNormal p (e.symm (e u)))∈projectionClosure K at h
    simpa only [e.symm_apply_apply] using h
  have hCne : C≠E := by
    intro hC
    apply hproper
    apply top_unique
    intro z _
    have hz : ((e.symm z : E) : G)∈C := by rw [hC]; exact (e.symm z).property
    obtain ⟨u,hu,he⟩ := hz
    have heq : u=e.symm z := Subtype.ext he
    change e u∈projectionClosure K at hu
    simpa only [heq,e.apply_symm_apply] using hu
  have hC : C=E⊓MulAction.stabilizer G x :=
    (primitive_stabilizer_interval x E C hCE hcap hnorm).resolve_right hCne
  apply le_antisymm _ (le_projectionClosure K)
  intro z hz
  apply (mem_pointStabilizerCoordinates k e x z).mpr
  have hm : ((e.symm z : E) : G)∈C := by
    refine ⟨e.symm z,?_,rfl⟩
    change e (e.symm z)∈projectionClosure K
    simpa only [e.apply_symm_apply] using hz
  rw [hC] at hm
  exact hm.2

/-- The two raw O'Nan--Scott degree forms follow from actual primitive
point-stabilizer maximality and the proved subdirect-product theorem. -/
theorem minimalNormal_pointStabilizer_degree_forms
    {G X T : Type} [Group G] [Group T] [Finite T] [IsSimpleGroup T]
    [MulAction G X] [FaithfulSMul G X] [Nontrivial X]
    [MulAction.IsPreprimitive G X]
    (E : Subgroup G) [E.Normal] (hE : IsMinimalNormalSubgroup E)
    [MulAction.IsPretransitive E X]
    (hT : IsCenterless T) (k : ℕ)
    (e : E ≃* (Fin k → T)) (x : X) :
    (∃ H : Subgroup T, H≠⊤ ∧ Nat.card X=H.index^k) ∨
    (∃ a : ℕ, k≤2*a ∧ Nat.card X=Nat.card T ^ a) := by
  let K := pointStabilizerCoordinates k e x
  by_cases honto : ∀ i, Function.Surjective
      ((Pi.evalMonoidHom (fun _ : Fin k => T) i).comp K.subtype)
  · exact Or.inr (subdirect_pointStabilizer_degree hT k e x honto)
  · push Not at honto
    obtain ⟨i,hi⟩ := honto
    have hHi : coordinateImage K i≠⊤ := by
      intro ht
      apply hi
      intro t
      have hm : t∈coordinateImage K i := by rw [ht]; trivial
      obtain ⟨z,hz,he⟩ := hm
      exact ⟨⟨z,hz⟩,he⟩
    have hproper : projectionClosure K≠⊤ := by
      intro ht
      apply hHi
      apply top_unique
      intro t _
      have hm : Pi.mulSingle i t∈projectionClosure K := by rw [ht]; trivial
      simpa only [Pi.mulSingle_eq_same] using (mem_projectionClosure K _).mp hm i
    have hclosure : projectionClosure K=K :=
      proper_projectionClosure_eq_stabilizer E hT k e x hproper
    have hcolor : ∀ j, (coordinateImage K j).index=(coordinateImage K i).index := by
      intro j
      apply minimalNormal_invariant_color_constant E hE hT k e x
        (fun q => (coordinateImage K q).index) ?_ j i
      intro p hp q
      exact coordinateImage_index_automorphism hT K (coordinateConjugation E k e p)
        (coordinateConjugation_preserves_stabilizer E k e x p hp) q
    left
    refine ⟨coordinateImage K i,hHi,?_⟩
    calc
      Nat.card X = K.index := (pointStabilizerCoordinates_index k e x).symm
      _ = (projectionClosure K).index := congrArg Subgroup.index hclosure.symm
      _ = (coordinateImage K i).index^k := projectionClosure_index k K _ hcolor

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
