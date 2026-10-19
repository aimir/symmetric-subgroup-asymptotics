import SymmetricSubgroupAsymptotics.MarkedC4OriginalGraphAnnihilators

/-! The actual graph-first quotient as a product of actual factor quotients.
The global mark group is not duplicated or quotiented. The normalized graph
is physically subdirect and has trivial isolated physical intersections.
These are constructed hypotheses for the genuine Case-I/II partition. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NormalizedCharacterGraph
open FiniteOrbitWordShapes FiniteBinaryWordTargets

variable {C b : ℕ} (T : Target C b) {M : Type} [Group M] (f : T.image →* M)
local instance factorNormal (i : Fin T.shape.length.val) :
    (OriginalGraphAnnihilators.factor T f i).Normal :=
  OriginalGraphAnnihilators.factor_normal T f i

abbrev Factor (i : Fin T.shape.length.val) :=
  T.letters i ⧸ OriginalGraphAnnihilators.factor T f i
abbrev Physical := ∀ i : Fin T.shape.length.val,Factor T f i

def physicalMap : Product T.letters →* Physical T f where
  toFun v i := QuotientGroup.mk' (OriginalGraphAnnihilators.factor T f i) (v i)
  map_one' := by funext i; exact (QuotientGroup.mk' _).map_one
  map_mul' v w := by funext i; exact (QuotientGroup.mk' _).map_mul (v i) (w i)

def quotientMap : (Product T.letters × M) →* (Physical T f × M) :=
  (physicalMap T f).prodMap (MonoidHom.id M)

def graph : Subgroup (Physical T f × M) :=
  (OriginalGraphAnnihilators.graph T f).map (quotientMap T f)

theorem kernel_le_original_graph : (quotientMap T f).ker ≤
    OriginalGraphAnnihilators.graph T f := by
  intro z hz
  have he := MonoidHom.mem_ker.mp hz
  have hp : z.1 ∈ OriginalGraphAnnihilators.physicalProduct T f := by
    intro i _
    apply (QuotientGroup.eq_one_iff (N := OriginalGraphAnnihilators.factor T f i) (z.1 i)).mp
    exact congrArg (fun q : Physical T f × M => q.1 i) he
  have hm : z.2=1 := congrArg Prod.snd he
  have ha := OriginalGraphAnnihilators.product_le_annihilator T f hp
  change (z.1,1) ∈ OriginalGraphAnnihilators.graph T f at ha
  have hz : (z.1,1)=z := Prod.ext rfl hm.symm
  exact hz ▸ ha

/-- Exact ORIGINAL graph recovery survives the product-quotient chart. -/
theorem recover : (graph T f).comap (quotientMap T f)=OriginalGraphAnnihilators.graph T f :=
  Subgroup.comap_map_eq_self (kernel_le_original_graph T f)

def projection (i : Fin T.shape.length.val) : graph T f →* Factor T f i :=
  (Pi.evalMonoidHom (Factor T f) i).comp
    ((MonoidHom.fst (Physical T f) M).comp (graph T f).subtype)

/-- Every actual physical quotient factor is still fully projected onto. -/
theorem projection_surjective (i : Fin T.shape.length.val) :
    Function.Surjective (projection T f i) := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (OriginalGraphAnnihilators.factor T f i) q
  obtain ⟨h,hh⟩ := T.subdirect i g
  refine ⟨⟨quotientMap T f (OriginalGraphAnnihilators.graphHom T f h),
    ⟨OriginalGraphAnnihilators.graphHom T f h,⟨h,rfl⟩,rfl⟩⟩,?_⟩
  exact congrArg (QuotientGroup.mk' (OriginalGraphAnnihilators.factor T f i)) hh

/-- No isolated physical factor survives: the annihilator was selected from
THIS graph, before quotienting. Shared marks are retained in one coordinate. -/
theorem isolated_eq_one (i : Fin T.shape.length.val) (q : Factor T f i)
    (hq : (Pi.mulSingle i q,1) ∈ graph T f) : q=1 := by
  obtain ⟨z,hz,he⟩ := hq
  obtain ⟨h,rfl⟩ := hz
  have hm : f h=1 := congrArg Prod.snd he
  have hi : QuotientGroup.mk' (OriginalGraphAnnihilators.factor T f i) (h.val i)=q := by
    simpa only [Pi.mulSingle_eq_same] using
      congrArg (fun v : Physical T f × M => v.1 i) he
  have hother (j : Fin T.shape.length.val) (hji : j≠i) :
      h.val j ∈ OriginalGraphAnnihilators.factor T f j := by
    apply (QuotientGroup.eq_one_iff (N := OriginalGraphAnnihilators.factor T f j) (h.val j)).mp
    have hj := congrArg (fun v : Physical T f × M => v.1 j) he
    simpa [quotientMap,physicalMap,OriginalGraphAnnihilators.graphHom,
      Pi.mulSingle,hji,Ne.symm hji] using hj
  let w : Product T.letters := Function.update h.val i 1
  have hw : w ∈ OriginalGraphAnnihilators.physicalProduct T f := by
    intro j _
    by_cases hji : j=i
    · subst j
      simpa only [w,Function.update_self] using (OriginalGraphAnnihilators.factor T f i).one_mem
    · simpa only [w,Function.update_of_ne hji] using hother j hji
  have hv : h.val ∈ OriginalGraphAnnihilators.annihilator T f := by
    change (h.val,1) ∈ (OriginalGraphAnnihilators.graphHom T f).range
    exact ⟨h,Prod.ext rfl hm⟩
  have hw' := OriginalGraphAnnihilators.product_le_annihilator T f hw
  have hc := (OriginalGraphAnnihilators.annihilator T f).mul_mem hv
    ((OriginalGraphAnnihilators.annihilator T f).inv_mem hw')
  have hs : h.val*w⁻¹=Pi.mulSingle i (h.val i) := by
    funext j
    by_cases hji : j=i
    · subst j
      simp [w]
    · simp [w,Pi.mulSingle,hji,Ne.symm hji]
  have hn : h.val i ∈ OriginalGraphAnnihilators.factor T f i := by
    change Pi.mulSingle i (h.val i) ∈ OriginalGraphAnnihilators.annihilator T f
    exact hs ▸ hc
  exact hi.symm.trans ((QuotientGroup.eq_one_iff
    (N := OriginalGraphAnnihilators.factor T f i) (h.val i)).mpr hn)

end SymmetricSubgroupAsymptotics.MarkedC4.NormalizedCharacterGraph
