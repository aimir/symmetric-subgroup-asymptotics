import SymmetricSubgroupAsymptotics.MarkedC4ActualSubdirectFiltration

/-! Actual efficient-generator recovery for a literal subdirect subgroup.
ALL choices of lifts of the same actual diagonal normal generators recover
that subgroup. This is the incidence input needed to divide the number of
ambient arrays by the multiplicity of lift choices, rather than paying a
separate worst-case count for each source column. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualEfficientLiftRecovery
open ActualSubdirectFiltration

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (H : Subgroup (∀ i,F i))
  (hsurj : ∀ i,Function.Surjective (coordinate F H i))
def normalGenerators (i : Fin t) : Finset (F i) := by
  letI : (diagonal F H i).Normal := diagonalNormal F H hsurj i
  exact Classical.choose (normalGen_spec (diagonal F H i))

theorem normalGenerators_spec (i : Fin t) :
    (normalGenerators F H hsurj i).card=normalGen (diagonal F H i) ∧
    (normalGenerators F H hsurj i : Set (F i)) ⊆ diagonal F H i ∧
    Subgroup.normalClosure (normalGenerators F H hsurj i : Set (F i))=diagonal F H i := by
  letI : (diagonal F H i).Normal := diagonalNormal F H hsurj i
  exact Classical.choose_spec (normalGen_spec (diagonal F H i))

abbrev Position := Σ i : Fin t,{q : F i // q∈normalGenerators F H hsurj i}
abbrev LiftArray := ∀ i : Fin t,∀ q : {q : F i // q∈normalGenerators F H hsurj i},
  {h : H // h∈«prefix» F H (i.val+1) ∧ coordinate F H i h=q.val}

/-- Every diagonal generator has actual lifts in its original prefix. -/
theorem liftArray_nonempty : Nonempty (LiftArray F H hsurj) := by
  have hn (i : Fin t) (q : {q : F i // q∈normalGenerators F H hsurj i}) :
      ∃ h : H,h∈«prefix» F H (i.val+1) ∧ coordinate F H i h=q.val :=
    (normalGenerators_spec F H hsurj i).2.1 q.property
  exact ⟨fun i q => ⟨Classical.choose (hn i q),Classical.choose_spec (hn i q)⟩⟩

def generatingSet (a : LiftArray F H hsurj) : Set H :=
  Set.range (fun z : Position F H hsurj => (a z.1 z.2).val)

/-- The proof applies to EVERY array of actual lifts, not just a selected
existence witness. It retains the original subgroup and its prefix kernels. -/
theorem normalClosure_eq_top (a : LiftArray F H hsurj) :
    Subgroup.normalClosure (generatingSet F H hsurj a)=⊤ := by
  let C := Subgroup.normalClosure (generatingSet F H hsurj a)
  have hc : ∀ m : ℕ,m≤t → «prefix» F H m≤C := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [prefix_zero]
      exact bot_le
    | succ m ih =>
      intro hm
      let i : Fin t := ⟨m,by omega⟩
      let V := Subgroup.normalClosure
        (Set.range (fun q : {q : F i // q∈normalGenerators F H hsurj i} => (a i q).val))
      have hVU : V≤«prefix» F H (i.val+1) := by
        apply Subgroup.normalClosure_le_normal
        rintro x ⟨q,rfl⟩
        exact (a i q).property.1
      have hVC : V≤C := by
        apply Subgroup.normalClosure_mono
        rintro x ⟨q,rfl⟩
        exact ⟨⟨i,q⟩,rfl⟩
      letI : (V.map (coordinate F H i)).Normal :=
        Subgroup.Normal.map inferInstance _ (hsurj i)
      have hDV : diagonal F H i≤V.map (coordinate F H i) := by
        rw [← (normalGenerators_spec F H hsurj i).2.2]
        apply Subgroup.normalClosure_le_normal
        intro q hq
        let q' : {q : F i // q∈normalGenerators F H hsurj i} := ⟨q,hq⟩
        exact ⟨(a i q').val,Subgroup.subset_normalClosure ⟨q',rfl⟩,(a i q').property.2⟩
      intro x hx
      have hxU : x∈«prefix» F H (i.val+1) := hx
      have hxD : coordinate F H i x∈diagonal F H i := ⟨x,hxU,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hDV hxD
      have hk : y⁻¹*x∈«prefix» F H m := by
        apply prefix_kernel F H i
        · exact («prefix» F H (i.val+1)).mul_mem
            ((«prefix» F H (i.val+1)).inv_mem (hVU hy)) hxU
        · rw [map_mul,map_inv,hyx,inv_mul_cancel]
      have hmem : y*(y⁻¹*x)∈C := C.mul_mem (hVC hy) (ih (by omega) hk)
      simpa only [mul_inv_cancel_left] using hmem
  apply top_unique
  rw [← prefix_full F H]
  exact hc t le_rfl

/-- Finite nilpotence turns normal generation into ordinary generation.
This is applicable to the actual binary subdirect groups in Case I. -/
theorem closure_eq_top [Group.IsNilpotent H] (a : LiftArray F H hsurj) :
    Subgroup.closure (generatingSet F H hsurj a)=⊤ := by
  rcases IsCoatomic.eq_top_or_exists_le_coatom (α := Subgroup H)
      (Subgroup.closure (generatingSet F H hsurj a)) with h | ⟨M,hM,hle⟩
  · exact h
  · exfalso
    letI : M.Normal :=
      Subgroup.NormalizerCondition.normal_of_coatom (H := M)
        Group.normalizerCondition_of_isNilpotent hM
    have hn : Subgroup.normalClosure (generatingSet F H hsurj a)≤M :=
      Subgroup.normalClosure_le_normal (Subgroup.subset_closure.trans hle)
    rw [normalClosure_eq_top F H hsurj a] at hn
    exact hM.1 (eq_top_iff.mpr hn)

def ambientArray (a : LiftArray F H hsurj) : Position F H hsurj → ∀ i,F i :=
  fun z => (a z.1 z.2).val.val

/-- Literal recovery in the original physical product. This supplies
pairwise disjoint incidence fibres for distinct actual source subgroups. -/
theorem recover [Group.IsNilpotent H] (a : LiftArray F H hsurj) :
    Subgroup.closure (Set.range (ambientArray F H hsurj a))=H := by
  have he : Set.range (ambientArray F H hsurj a)=
      H.subtype '' generatingSet F H hsurj a := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨(a z.1 z.2).val,⟨z,rfl⟩,rfl⟩
    · rintro ⟨h,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
  rw [he,← MonoidHom.map_closure,closure_eq_top F H hsurj a,
    ← MonoidHom.range_eq_map,H.range_subtype]

end SymmetricSubgroupAsymptotics.MarkedC4.ActualEfficientLiftRecovery
