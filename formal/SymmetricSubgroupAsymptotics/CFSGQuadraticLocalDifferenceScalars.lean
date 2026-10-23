import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalPieceRestriction

/-! A local linear representative on a genuine singular plane couples
the scalars of two image rays and their fixed difference ray. This
generic statement keeps concrete fixed-space elaboration out of the
linear scalar argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticLocalDifferenceScalars
open CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_scalars (Q : QuadraticForm K V) (f : Points Q ≃ Points Q)
    (hlinear : ∀ W : Subspaces Q,
      Nonempty (SemilinearPiece Q f W (RingEquiv.refl K)))
    (v w v' w' : V) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hd0 : v - w ≠ 0)
    (hvQ : Q v = 0) (hwQ : Q w = 0) (hdQ : Q (v - w) = 0)
    (hfv : (f (ray Q v hv0 hvQ)).val = Submodule.span K {v'})
    (hfw : (f (ray Q w hw0 hwQ)).val = Submodule.span K {w'})
    (hfd : f (ray Q (v - w) hd0 hdQ) = ray Q (v - w) hd0 hdQ) :
    ∃ alpha beta gamma : K, alpha ≠ 0 ∧
      alpha • v' - beta • w' = gamma • (v - w) := by
  classical
  have hvw : Q.polarBilin v w = 0 := by
    have he : Q (v - w) = -Q.polarBilin v w := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q v (-w), Q.map_neg, hvQ, hwQ,
        zero_add, zero_add]
      exact map_neg (Q.polarBilin v) w
    exact neg_eq_zero.mp (he.symm.trans hdQ)
  have hWs : ∀ z ∈ Submodule.span K {v, w}, Q z = 0 := by
    intro z hz
    obtain ⟨r, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [QuadraticMap.map_add Q (r • v) (t • w)]
    change Q (r • v) + Q (t • w) + Q.polarBilin (r • v) (t • w) = 0
    simp only [Q.map_smul, hvQ, hwQ, map_smul,
      LinearMap.smul_apply, hvw, smul_eq_mul, mul_zero, add_zero]
  let W : Subspaces Q := ⟨Submodule.span K {v, w}, hWs⟩
  have hvW : v ∈ W.val := Submodule.subset_span (by simp)
  have hwW : w ∈ W.val := Submodule.subset_span (by simp)
  let X : W.val := ⟨v, hvW⟩
  let Y : W.val := ⟨w, hwW⟩
  let D : W.val := ⟨v - w, W.val.sub_mem hvW hwW⟩
  have hX0 : X ≠ 0 := fun he => hv0 (congrArg (fun x : W.val => x.val) he)
  have hY0 : Y ≠ 0 := fun he => hw0 (congrArg (fun x : W.val => x.val) he)
  have hD0 : D ≠ 0 := fun he => hd0 (congrArg (fun x : W.val => x.val) he)
  let F := Classical.choice (hlinear W)
  have hFX := F.point X hX0
  change Submodule.span K {F.map X} = (f (ray Q v hv0 hvQ)).val at hFX
  rw [hfv] at hFX
  have hmX : F.map X ∈ Submodule.span K {v'} :=
    hFX ▸ Submodule.mem_span_singleton_self _
  obtain ⟨alpha, hAlpha⟩ := Submodule.mem_span_singleton.mp hmX
  have hAlpha0 : alpha ≠ 0 := by
    intro he
    have hz : F.map X = F.map 0 := by rw [← hAlpha, he, zero_smul, map_zero]
    exact hX0 (F.injective hz)
  have hFY := F.point Y hY0
  change Submodule.span K {F.map Y} = (f (ray Q w hw0 hwQ)).val at hFY
  rw [hfw] at hFY
  have hmY : F.map Y ∈ Submodule.span K {w'} :=
    hFY ▸ Submodule.mem_span_singleton_self _
  obtain ⟨beta, hBeta⟩ := Submodule.mem_span_singleton.mp hmY
  have hFD := F.point D hD0
  change Submodule.span K {F.map D} = (f (ray Q (v - w) hd0 hdQ)).val at hFD
  rw [hfd] at hFD
  change Submodule.span K {F.map D} = Submodule.span K {v - w} at hFD
  have hmD : F.map D ∈ Submodule.span K {v - w} :=
    hFD ▸ Submodule.mem_span_singleton_self _
  obtain ⟨gamma, hGamma⟩ := Submodule.mem_span_singleton.mp hmD
  refine ⟨alpha, beta, gamma, hAlpha0, ?_⟩
  calc
    alpha • v' - beta • w' = F.map X - F.map Y :=
      congrArg₂ (fun x y : V => x - y) hAlpha hBeta
    _ = F.map D := (F.map.map_sub X Y).symm
    _ = gamma • (v - w) := hGamma.symm

end SymmetricSubgroupAsymptotics.CFSGQuadraticLocalDifferenceScalars
