import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourPerfectProjection

/-! The proved proper middle parabolic descends to the SAME pinned
original Ree model when m>0. Its source contains the full quotient
kernel, proved central via the actual derived/full-centre definition.
The centre lies in the actual Borel by ambient regular-normalizer
reflection; no trivial-centre assertion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleParabolic
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourFixedAmbientHom
open CFSGReeFFourRegularFixedPositive CFSGRegularElementSylowPreimage
open CFSGFFourE6AmbientPositiveSylow CFSGTwistedE6GeckAmbientPositiveSylow
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourPerfectProjection
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourMiddleParabolicFlag
open CFSGReeFFourMiddleParabolicCardinality CFSGReeFFourParabolicIndexNumerics
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem normalizer_positive_le_borel (m : ℕ) :
    Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m))≤fixedBorel m := by
  intro g hg
  have hU : ((ambientSylow (Field m) 2 : Subgroup
      (CFSGFFourE6AmbientPositiveSylow.AmbientGroup (Field m))).comap (fixedAmbientHom m))=
        fixedPositive m := by
    rw [ambientSylow_coe]
    exact (fixedPositive_eq_preimage m).symm
  rw [←hU] at hg
  have hnA := preimage_normalizer_le_comap_normalizer (ambientSylow (Field m) 2)
    (fixedAmbientHom m) (regularFixed m) (fixedAmbientHom_regular_positive m)
    (fixedAmbientHom_regular_unique m) hg
  exact CFSGTwistedE6GeckAmbientPositiveSylow.ambient_normalizer_map_le (Field m)
    ⟨fixedAmbientHom m g,hnA,rfl⟩

theorem center_le_borel (m : ℕ) : Subgroup.center (originalModelFixed m)≤fixedBorel m :=
  (Subgroup.center_le_normalizer (fixedPositive m : Set (originalModelFixed m))).trans
    (normalizer_positive_le_borel m)

theorem fixedToOriginal_kernel_le_center (m : ℕ) (hm : 0<m) :
    (fixedToOriginal m hm).ker≤Subgroup.center (originalModelFixed m) := by
  intro x hx
  have he : fixedToOriginal m hm x=1 := hx
  have hq : (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))))
      (fixedToDerived m hm x)=1 := by
    apply (originalReeEquiv m).symm.injective
    calc
      _=fixedToOriginal m hm x := rfl
      _=1 := he
      _=(originalReeEquiv m).symm 1 := (map_one (originalReeEquiv m).symm).symm
  have hc : fixedToDerived m hm x∈Subgroup.center (commutator (originalModelFixed m)) :=
    (QuotientGroup.eq_one_iff _).mp hq
  apply Subgroup.mem_center_iff.mpr
  intro y
  exact congrArg (fun z : commutator (originalModelFixed m)=>z.val)
    (Subgroup.mem_center_iff.mp hc (fixedToDerived m hm y))

theorem fixedToOriginal_kernel_le_parabolic (m : ℕ) (hm : 0<m) :
    (fixedToOriginal m hm).ker≤middleParabolic m := by
  have hBP : fixedBorel m≤middleParabolic m := by
    rw [fixedBorel_eq_sup]
    exact le_sup_left
  exact ((fixedToOriginal_kernel_le_center m hm).trans (center_le_borel m)).trans hBP

def originalMiddleParabolic (m : ℕ) (hm : 0<m) : Subgroup (CFSG.Models.ReeF4 m) :=
  (middleParabolic m).map (fixedToOriginal m hm)

theorem originalMiddleParabolic_ne_top (m : ℕ) (hm : 0<m) :
    originalMiddleParabolic m hm≠⊤ := by
  intro he
  have hc := congrArg (fun H : Subgroup (CFSG.Models.ReeF4 m)=>H.comap (fixedToOriginal m hm)) he
  change ((middleParabolic m).map (fixedToOriginal m hm)).comap (fixedToOriginal m hm)=
    (⊤ : Subgroup (CFSG.Models.ReeF4 m)).comap (fixedToOriginal m hm) at hc
  rw [Subgroup.comap_top,Subgroup.comap_map_eq_self (fixedToOriginal_kernel_le_parabolic m hm)] at hc
  exact middleParabolic_ne_top m hc

theorem originalMiddleParabolic_index (m : ℕ) (hm : 0<m) :
    (originalMiddleParabolic m hm).index=(middleParabolic m).index :=
  (middleParabolic m).index_map_eq (fixedToOriginal_surjective m hm)
    (fixedToOriginal_kernel_le_parabolic m hm)

theorem originalMiddleParabolic_index_le (m : ℕ) (hm : 0<m) :
    (originalMiddleParabolic m hm).index ≤ indexUpper (2^(2*m+1)) := by
  rw [originalMiddleParabolic_index]
  exact middleParabolic_index_le m

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleParabolic
