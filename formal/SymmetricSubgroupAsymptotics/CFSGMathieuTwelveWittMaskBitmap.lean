import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveYRawPointMaskCoding

/-! Necessary bitmap coding for the132 SAME original Witt hexads. A false
bit excludes membership. No converse or collision-free encoding is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveWittMaskBitmap
open CFSG.Certificates.Mathieu12 M12Certificates.WittDesign
open CFSGMathieuTwelveYRawPointMaskCoding
open CFSGMathieuTwelveYCentralizerFiniteEncoding

def bitmap : ℕ := 13182040934309431001038897942698675127651386650862675421323546911912069560360596188483233279038657527162156202156555215692648326967856093113780002704394036939504427633916034513597635079419776145205533796344219396762181132911433699414419073380141271446881252130267309675697772227355940577380439559519309295271736134247242631021810805511167952277851950543684542730924940493623107626515789922836892906420487874819472927469052501809084318256440883949592427807759849509670445667164322726468606547031093732084860317822195582760443592984027363649092178698181869543460819443237843379423889187991128511428535780584202605429973567230661427319686018905779287004872147056425585645035441971249211824718978730069771084853675145255736785312028556315969657142716185871722309227117889162743233913824949681565168592443527941415504733837399942218598590897461535539012118496566428423500092803542204015236920462407881484143686597236356058011925785894088641435401605638588123640739385642226936356458132260352876560170619801784307351059120838129188751721086245145783627727154736915426498620498464104210999465588259973813803399520319474585557991846375627396484426499432730453188610008408563157015397462401878167918439505147723776

private def chunk (start : ℕ) : Bool :=
  (List.range 33).all (fun j => bitmap.testBit
    (blockMask (wittBlockAt ⟨(start+j)%132,Nat.mod_lt _ (by decide)⟩)))

private theorem chunk_0 : chunk 0 = true := by
  decide +kernel

private theorem chunk_33 : chunk 33 = true := by
  decide +kernel

private theorem chunk_66 : chunk 66 = true := by
  decide +kernel

private theorem chunk_99 : chunk 99 = true := by
  decide +kernel

private theorem chunk_sound (start : ℕ) (h : chunk start = true)
    (k : Fin 132) (hlo : start ≤ k.val) (hhi : k.val < start+33) :
    bitmap.testBit (blockMask (wittBlockAt k)) = true := by
  have hm : k.val-start ∈ List.range 33 := List.mem_range.mpr (by omega)
  have ht := List.all_eq_true.mp h (k.val-start) hm
  have he : (⟨(start+(k.val-start))%132,Nat.mod_lt _ (by decide)⟩ : Fin 132) = k := by
    apply Fin.ext
    change (start+(k.val-start))%132 = k.val
    have hk := k.isLt
    omega
  simpa only [he] using ht

theorem original_witt_bits (k : Fin 132) :
    bitmap.testBit (blockMask (wittBlockAt k)) = true := by
  if h0 : k.val < 33 then
    exact chunk_sound 0 chunk_0 k (Nat.zero_le _) (by omega)
  else if h1 : k.val < 66 then
    exact chunk_sound 33 chunk_33 k (by omega) (by omega)
  else if h2 : k.val < 99 then
    exact chunk_sound 66 chunk_66 k (by omega) (by omega)
  else
    exact chunk_sound 99 chunk_99 k (by omega) k.isLt

theorem image_mask_eq (c : Fin 1944) (B : Block) :
    blockMask (blockMap (indexedChart c) B) = ∑ p ∈ B, 2^(rawPoint c.val p.val) := by
  unfold blockMask blockMap
  rw [Finset.sum_image (indexedChart c).injective.injOn]
  apply Finset.sum_congr rfl
  intro p _
  rw [rawPoint_eq]

theorem rejects_of_raw_mask_false (c : Fin 1944) (B : Block)
    (h : bitmap.testBit (∑ p ∈ B, 2^(rawPoint c.val p.val)) = false) :
    blockMap (indexedChart c) B ∉ wittBlocks := by
  apply not_mem_of_bit_false bitmap original_witt_bits
  rw [image_mask_eq]
  exact h

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveWittMaskBitmap
