import SymmetricSubgroupAsymptotics.MarkedC4ActualQuotientTableauMenus

/-! Actual isolated intersections under successive physical projections.
They increase in each ORIGINAL factor, so all normalization changes across
the recursive peel occupy one finite monotone-chain menu, independent of r. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualPeelNormalChains

variable {t : ℕ} (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
  {M : Type} [Group M] (J : Subgroup ((∀ i,F i) × M))

def coordinate (i : Fin t) : J →* F i :=
  (Pi.evalMonoidHom F i).comp ((MonoidHom.fst (∀ i,F i) M).comp J.subtype)
def marker : J →* M := (MonoidHom.snd (∀ i,F i) M).comp J.subtype

def isolatedKernel (S : Finset (Fin t)) (i : Fin t) : Subgroup J :=
  (marker F J).ker ⊓ ⨅ j : {j : Fin t // j∈S ∧ j≠i},(coordinate F J j.val).ker
instance kernelNormal (S : Finset (Fin t)) (i : Fin t) : (isolatedKernel F J S i).Normal := by
  unfold isolatedKernel
  letI : (⨅ j : {j : Fin t // j∈S ∧ j≠i},(coordinate F J j.val).ker).Normal :=
    Subgroup.normal_iInf_normal (fun _ => inferInstance)
  infer_instance

def factor (S : Finset (Fin t)) (i : Fin t) : Subgroup (F i) :=
  (isolatedKernel F J S i).map (coordinate F J i)

omit [∀ i,Finite (F i)] in
theorem factor_normal (hfull : ∀ i,Function.Surjective (coordinate F J i))
    (S : Finset (Fin t)) (i : Fin t) : (factor F J S i).Normal :=
  Subgroup.Normal.map inferInstance (coordinate F J i) (hfull i)

omit [∀ i,Finite (F i)] in
theorem factor_antitone (i : Fin t) : Antitone (fun S : Finset (Fin t) => factor F J S i) := by
  intro S T hST
  apply Subgroup.map_mono
  intro x hx
  refine ⟨hx.1,?_⟩
  apply Subgroup.mem_iInf.mpr
  intro j
  exact (Subgroup.mem_iInf.mp hx.2) ⟨j.val,hST j.property.1,j.property.2⟩

def remaining (e : Equiv.Perm (Fin t)) (m : ℕ) : Finset (Fin t) :=
  Finset.univ.filter (fun i => m≤(e.symm i).val)

theorem remaining_antitone (e : Equiv.Perm (Fin t)) : Antitone (remaining e) := by
  intro m n hmn i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmn.trans (Finset.mem_filter.mp hi).2⟩

/-- Actual isolated-normal chains for the SAME evolving marked subgroup.
The rows keep their original types and order even when quotients change. -/
def normalChains (e : Equiv.Perm (Fin t)) : ActualQuotientTableauMenus.RowMenu F :=
  fun i => ⟨fun m : Fin t => factor F J (remaining e m.val) i,by
    intro m n hmn
    exact factor_antitone F J i (remaining_antitone e hmn)⟩

theorem normalChains_normal (hfull : ∀ i,Function.Surjective (coordinate F J i))
    (e : Equiv.Perm (Fin t)) (i m : Fin t) :
    ((normalChains F J e i).val m).Normal := factor_normal F J hfull _ i

end SymmetricSubgroupAsymptotics.MarkedC4.ActualPeelNormalChains
