import SymmetricSubgroupAsymptotics.MarkedC4ActualPeelNormalChains
import SymmetricSubgroupAsymptotics.MarkedC4ActualFullPhysicalWordPeel

/-! Whole-word normalization of the ACTUAL enlarged marked subgroup.
Its isolated normals are selected from this same subgroup; the same global
marker is retained. Projection followed by normalization therefore recovers
every recursive state and its monotone original normal-chain labels. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualWholeWordNormalization
open ActualFullPhysicalWordPeel

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  (M : Type) [Group M] (J : Family F M)

def factor (i : Fin t) : Subgroup (F i) := ActualPeelNormalChains.factor F J.val Finset.univ i
instance factorNormal (i : Fin t) : (factor F M J i).Normal :=
  ActualPeelNormalChains.factor_normal F J.val J.property Finset.univ i

theorem mem_factor_iff (i : Fin t) (g : F i) :
    g∈factor F M J i ↔ (Pi.mulSingle i g,1)∈J.val := by
  constructor
  · rintro ⟨h,hh,he⟩
    have hm : h.val.2=1 := hh.1
    have hother (j : Fin t) (hji : j≠i) : h.val.1 j=1 :=
      (Subgroup.mem_iInf.mp hh.2) ⟨j,Finset.mem_univ _,hji⟩
    have hs : h.val=(Pi.mulSingle i g,1) := by
      apply Prod.ext
      · funext j
        by_cases hji : j=i
        · subst j
          simpa only [Pi.mulSingle_eq_same] using he
        · simpa [Pi.mulSingle,hji,Ne.symm hji] using hother j hji
      · exact hm
    exact hs ▸ h.property
  · intro hg
    let h : J.val := ⟨(Pi.mulSingle i g,1),hg⟩
    refine ⟨h,⟨?_,?_⟩,?_⟩
    · rfl
    · apply Subgroup.mem_iInf.mpr
      intro j
      change (Pi.mulSingle i g) j.val=1
      simp [Pi.mulSingle,j.property.2,Ne.symm j.property.2]
    · change (Pi.mulSingle i g) i=g
      simp only [Pi.mulSingle_eq_same]

def unmarked : (∀ i,F i) →* ((∀ i,F i) × M) where
  toFun x := (x,1)
  map_one' := rfl
  map_mul' _ _ := by simp
def physicalProduct : Subgroup (∀ i,F i) := Subgroup.pi Set.univ (factor F M J)

theorem product_le_annihilator : physicalProduct F M J≤J.val.comap (unmarked F M) := by
  apply Subgroup.pi_le_iff.mpr
  intro i
  rintro x ⟨g,hg,rfl⟩
  exact (mem_factor_iff F M J i g).mp hg

abbrev Factors (i : Fin t) := F i ⧸ factor F M J i
def physicalMap : (∀ i,F i) →* (∀ i,Factors F M J i) where
  toFun x i := QuotientGroup.mk' (factor F M J i) (x i)
  map_one' := by funext i; exact (QuotientGroup.mk' _).map_one
  map_mul' x y := by funext i; exact (QuotientGroup.mk' _).map_mul (x i) (y i)
def quotientMap : ((∀ i,F i) × M) →* ((∀ i,Factors F M J i) × M) :=
  (physicalMap F M J).prodMap (MonoidHom.id M)
def normalized : Subgroup ((∀ i,Factors F M J i) × M) := J.val.map (quotientMap F M J)

theorem kernel_le : (quotientMap F M J).ker≤J.val := by
  intro z hz
  have he := MonoidHom.mem_ker.mp hz
  have hp : z.1∈physicalProduct F M J := by
    intro i hi
    apply (QuotientGroup.eq_one_iff (N := factor F M J i) (z.1 i)).mp
    exact congrArg (fun x : (∀ i,Factors F M J i) × M => x.1 i) he
  have hm : z.2=1 := congrArg (fun x : (∀ i,Factors F M J i) × M => x.2) he
  have hj : (z.1,1)∈J.val := product_le_annihilator F M J hp
  exact (show (z.1,1)=z from Prod.ext rfl hm.symm) ▸ hj

theorem recover : (normalized F M J).comap (quotientMap F M J)=J.val :=
  Subgroup.comap_map_eq_self (kernel_le F M J)

theorem physical_full (i : Fin t) : Function.Surjective
    (fun h : normalized F M J => h.val.1 i) := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (factor F M J i) q
  obtain ⟨h,hh⟩ := J.property i g
  refine ⟨⟨quotientMap F M J h.val,⟨h.val,h.property,rfl⟩⟩,?_⟩
  exact congrArg (QuotientGroup.mk' (factor F M J i)) hh

theorem isolated_eq_one (i : Fin t) (q : Factors F M J i)
    (hq : (Pi.mulSingle i q,1)∈normalized F M J) : q=1 := by
  obtain ⟨z,hz,he⟩ := hq
  have hm : z.2=1 := congrArg (fun x : (∀ i,Factors F M J i) × M => x.2) he
  have hi : QuotientGroup.mk' (factor F M J i) (z.1 i)=q := by
    simpa only [Pi.mulSingle_eq_same] using
      congrArg (fun x : (∀ i,Factors F M J i) × M => x.1 i) he
  have hother (j : Fin t) (hji : j≠i) : z.1 j∈factor F M J j := by
    apply (QuotientGroup.eq_one_iff (N := factor F M J j) (z.1 j)).mp
    have hj := congrArg (fun x : (∀ i,Factors F M J i) × M => x.1 j) he
    simpa [quotientMap,physicalMap,Pi.mulSingle,hji,Ne.symm hji] using hj
  let w : ∀ j,F j := Function.update z.1 i 1
  have hw : w∈physicalProduct F M J := by
    intro j hj
    by_cases hji : j=i
    · subst j
      simpa only [w,Function.update_self] using (factor F M J i).one_mem
    · simpa only [w,Function.update_of_ne hji] using hother j hji
  have hwm : (w,1)∈J.val := product_le_annihilator F M J hw
  have hc := J.val.mul_mem hz (J.val.inv_mem hwm)
  have hs : z*(w,1)⁻¹=(Pi.mulSingle i (z.1 i),1) := by
    apply Prod.ext
    · funext j
      by_cases hji : j=i
      · subst j
        simp [w]
      · simp [w,Pi.mulSingle,hji,Ne.symm hji]
    · simpa using hm
  have hn : z.1 i∈factor F M J i := (mem_factor_iff F M J i _).mpr (hs ▸ hc)
  exact hi.symm.trans ((QuotientGroup.eq_one_iff (N := factor F M J i) (z.1 i)).mpr hn)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualWholeWordNormalization
