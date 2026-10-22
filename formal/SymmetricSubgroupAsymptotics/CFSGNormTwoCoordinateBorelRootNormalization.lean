import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootCentral
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBorelEnvelope
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! The literal torus normalizes every original lattice-root subgroup,
and the literal Borel normalizes the dominant-root subgroup. These are
actual parameter calculations, with no normalizer-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBorelRootNormalization
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootTorusConjugation
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckBorelEnvelope
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateHighestRootCentral
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem torus_conjugate_rootSubgroup (K : Type) [Field K] (i : Fin r) (t : Kˣ)
    (k : Roots A) :
    (rootSubgroup A hd hs hp ho K k).map
      (MulAut.conj (parameterTorus A hs hp b₀ s₀ K i t)).toMonoidHom=
        rootSubgroup A hd hs hp ho K k := by
  let c : K := (t:K)^(integerPairing A (s₀ i : Roots A).val k.val)
  have hc : c≠0 := zpow_ne_zero _ t.ne_zero
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k y).mp hy
    change parameterTorus A hs hp b₀ s₀ K i t*selectedRootElement A hd hs hp ho K k a*
      (parameterTorus A hs hp b₀ s₀ K i t)⁻¹∈_
    rw [torus_conjugate_selected_root]
    exact (mem_rootSubgroup_iff_selected A hd hs hp ho K k _).mpr ⟨a*c,rfl⟩
  · intro hx
    obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mp hx
    refine ⟨selectedRootElement A hd hs hp ho K k (a/c),
      (mem_rootSubgroup_iff_selected A hd hs hp ho K k _).mpr ⟨a/c,rfl⟩,?_⟩
    change parameterTorus A hs hp b₀ s₀ K i t*selectedRootElement A hd hs hp ho K k (a/c)*
      (parameterTorus A hs hp b₀ s₀ K i t)⁻¹=selectedRootElement A hd hs hp ho K k a
    rw [torus_conjugate_selected_root]
    change selectedRootElement A hd hs hp ho K k (a/c*c)=_
    rw [div_mul_cancel₀ a hc]

theorem torusGroup_le_normalizer_root (K : Type) [Field K] (k : Roots A) :
    torusGroup A hs hp b₀ s₀ K≤Subgroup.normalizer (rootSubgroup A hd hs hp ho K k : Set _) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  exact congrArg (fun H : Subgroup ((Matrix ((b₀).support⊕Roots A)
    ((b₀).support⊕Roots A) K)ˣ)=> (H : Set ((Matrix ((b₀).support⊕Roots A)
      ((b₀).support⊕Roots A) K)ˣ)))
      (torus_conjugate_rootSubgroup A hd hs hp ho K i t k)

theorem positive_le_centralizer_root (K : Type) [Field K] (k : Roots A)
    (hk : ∀i,0≤k.val i)
    (hdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    PositiveGroup A hd hs hp ho K≤Subgroup.centralizer (rootSubgroup A hd hs hp ho K k : Set _) := by
  intro u hu
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mp hx
  exact Subgroup.mem_centralizer_iff.mp
    (positive_le_centralizer_dominant_root A hd hs hp ho K k hk hdom a hu)
    _ (Set.mem_singleton _)

theorem borel_le_normalizer_dominant_root (K : Type) [Field K] (k : Roots A)
    (hk : ∀i,0≤k.val i)
    (hdom : ∀i,0 ≤ integerPairing A k.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    borelEnvelope A hs hp b₀ s₀ K≤Subgroup.normalizer (rootSubgroup A hd hs hp ho K k : Set _) := by
  apply sup_le
  · exact (positive_le_centralizer_root A hd hs hp ho K k hk hdom).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact torusGroup_le_normalizer_root A hd hs hp ho K k

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBorelRootNormalization
