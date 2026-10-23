import SymmetricSubgroupAsymptotics.PermutationCycleCoboundary

/-! Matching actual cycle lengths constructs an actual point permutation
intertwining the two permutations. Its pullback preserves each matched
cycle product. No supplied point conjugator is required. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.PermutationCycleMatching
open PermutationCycleDecomposition PermutationCycleCoboundary

theorem finCongr_rotate {m n : ℕ} (h : m=n) (i : Fin m) :
    finCongr h (finRotate m i)=finRotate n (finCongr h i) := by
  subst n
  rfl

variable {I : Type*} [Finite I] (σ τ : Equiv.Perm I)
    (e : CycleIndex σ ≃ CycleIndex τ)
    (hlen : ∀c,cycleLength σ c=cycleLength τ (e c))

def pointEquiv : Equiv.Perm I :=
  (pointChart σ).symm.trans
    ((Equiv.sigmaCongr e (fun c => finCongr (hlen c))).trans (pointChart τ))

theorem pointEquiv_apply (c : CycleIndex σ) (i : Fin (cycleLength σ c)) :
    pointEquiv σ τ e hlen (pointChart σ ⟨c,i⟩)=
      pointChart τ ⟨e c,finCongr (hlen c) i⟩ := by
  change pointChart τ ((Equiv.sigmaCongr e (fun c => finCongr (hlen c)))
    ((pointChart σ).symm (pointChart σ ⟨c,i⟩)))=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem pointEquiv_intertwines (i : I) :
    pointEquiv σ τ e hlen (σ i)=τ (pointEquiv σ τ e hlen i) := by
  obtain ⟨⟨c,j⟩,rfl⟩ := (pointChart σ).surjective i
  calc
    pointEquiv σ τ e hlen (σ (pointChart σ ⟨c,j⟩))=
        pointEquiv σ τ e hlen (pointChart σ ⟨c,finRotate _ j⟩) :=
      congrArg (pointEquiv σ τ e hlen) (pointChart_rotate σ c j).symm
    _=pointChart τ ⟨e c,finCongr (hlen c) (finRotate _ j)⟩ :=
      pointEquiv_apply σ τ e hlen c _
    _=pointChart τ ⟨e c,finRotate _ (finCongr (hlen c) j)⟩ :=
      congrArg (fun k => pointChart τ ⟨e c,k⟩) (finCongr_rotate (hlen c) j)
    _=τ (pointChart τ ⟨e c,finCongr (hlen c) j⟩) :=
      pointChart_rotate τ (e c) _
    _=τ (pointEquiv σ τ e hlen (pointChart σ ⟨c,j⟩)) :=
      congrArg τ (pointEquiv_apply σ τ e hlen c j).symm

theorem pointEquiv_conjugate :
    pointEquiv σ τ e hlen * σ * (pointEquiv σ τ e hlen)⁻¹=τ := by
  ext i
  change pointEquiv σ τ e hlen (σ ((pointEquiv σ τ e hlen).symm i))=τ i
  rw [pointEquiv_intertwines,Equiv.apply_symm_apply]

theorem cycleProduct_transport {D : Type*} [CommGroup D] (f : I → D)
    (c : CycleIndex σ) :
    cycleProduct τ (fun i => f ((pointEquiv σ τ e hlen).symm i)) (e c)=
      cycleProduct σ f c := by
  let t := pointEquiv σ τ e hlen
  change (∏j : Fin (cycleLength τ (e c)),f (t.symm (pointChart τ ⟨e c,j⟩)))=
    ∏j : Fin (cycleLength σ c),f (pointChart σ ⟨c,j⟩)
  rw [← Equiv.prod_comp (finCongr (hlen c))
    (fun j => f (t.symm (pointChart τ ⟨e c,j⟩)))]
  apply Finset.prod_congr rfl
  intro j _
  have hp : t (pointChart σ ⟨c,j⟩)=
      pointChart τ ⟨e c,finCongr (hlen c) j⟩ := pointEquiv_apply σ τ e hlen c j
  have hs : t.symm (pointChart τ ⟨e c,finCongr (hlen c) j⟩)=
      pointChart σ ⟨c,j⟩ := by
    simpa only [Equiv.symm_apply_apply] using (congrArg t.symm hp).symm
  exact congrArg f hs

end SymmetricSubgroupAsymptotics.PermutationCycleMatching
