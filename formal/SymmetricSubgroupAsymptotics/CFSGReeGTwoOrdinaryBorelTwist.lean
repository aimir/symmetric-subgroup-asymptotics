import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBorel
import SymmetricSubgroupAsymptotics.CFSGReeGTwoSixWordTwist
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalTorus

/-! Stability of the actual ordinary B6 under the SAME original Ree
involution, and its precise action on the two simple Weyl words.
This is ordinary-cell covariance; fixed-cell factor descent is separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOrdinaryBorelTwist
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalAutomorphism
open CFSGReeGTwoSixWordTwist CFSGReeGTwoOriginalTorus
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoPositiveSixWord
open CFSGGTwoPositiveWordSubgroup CFSGGTwoOriginalBorel
open CFSGGTwoOriginalRankTwoTorus CFSGGTwoSimpleBruhatComplement
local notation "A" => CartanMatrix.G₂

theorem ree_positive_mem (m : ℕ) (g : Model A (Field m))
    (hg : g∈positiveWordGroup (Field m)) :
    reeAutomorphism m g∈positiveWordGroup (Field m) := by
  obtain ⟨x,rfl⟩ := hg
  rw [ree_modelWord]
  exact ⟨_,rfl⟩

theorem ree_positive_mem_iff (m : ℕ) (g : Model A (Field m)) :
    reeAutomorphism m g∈positiveWordGroup (Field m) ↔ g∈positiveWordGroup (Field m) := by
  constructor
  · intro hg
    have he := ree_positive_mem m _ hg
    rwa [reeAutomorphism_involutive] at he
  · exact ree_positive_mem m g

theorem ree_torus_mem (m : ℕ) (g : Model A (Field m)) (hg : g∈torus (Field m)) :
    reeAutomorphism m g∈torus (Field m) := by
  obtain ⟨t,rfl⟩ := hg
  rw [torusHom_apply,ree_torusPair]
  exact ⟨_,torusHom_apply (Field m) _⟩

theorem ree_borel_mem (m : ℕ) (g : Model A (Field m)) (hg : g∈borel (Field m)) :
    reeAutomorphism m g∈borel (Field m) := by
  obtain ⟨u,hu,t,ht,rfl⟩ := borel_factor (Field m) g hg
  rw [map_mul]
  exact (borel (Field m)).mul_mem
    (positive_le_borel (Field m) (ree_positive_mem m u hu))
    (torus_le_borel (Field m) (ree_torus_mem m t ht))

theorem ree_borel_mem_iff (m : ℕ) (g : Model A (Field m)) :
    reeAutomorphism m g∈borel (Field m) ↔ g∈borel (Field m) := by
  constructor
  · intro hg
    have he := ree_borel_mem m _ hg
    rwa [reeAutomorphism_involutive] at he
  · exact ree_borel_mem m g

private theorem ree_short_root (m : ℕ) (neg : Bool) (t : Field m) :
    reeAutomorphism m (modelRoot A (Field m) neg 0 t)=
      modelRoot A (Field m) neg 1 (alpha m t) := by
  exact reeAutomorphism_root m neg 0 t

private theorem ree_long_root (m : ℕ) (neg : Bool) (t : Field m) :
    reeAutomorphism m (modelRoot A (Field m) neg 1 t)=
      modelRoot A (Field m) neg 0 (beta m t) := by
  exact reeAutomorphism_root m neg 1 t

theorem ree_shortWord (m : ℕ) :
    reeAutomorphism m (shortWord (Field m))=(longWord (Field m))⁻¹ := by
  simp only [shortWord,map_mul,ree_short_root,map_one,map_neg]
  simp only [longWord,mul_inv_rev,modelRoot_inv,neg_neg,mul_assoc]

theorem ree_longWord (m : ℕ) :
    reeAutomorphism m (longWord (Field m))=(shortWord (Field m))⁻¹ := by
  simp only [longWord,map_mul,ree_long_root,map_one,map_neg]
  simp only [shortWord,mul_inv_rev,modelRoot_inv,neg_neg,mul_assoc]

theorem ree_simpleWeyl (m : ℕ) (i : Fin 2) :
    reeAutomorphism m (simpleWeyl (Field m) i)=
      (simpleWeyl (Field m) (CFSG.Models.reverseNode i))⁻¹ := by
  fin_cases i
  · exact ree_shortWord m
  · exact ree_longWord m

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOrdinaryBorelTwist
