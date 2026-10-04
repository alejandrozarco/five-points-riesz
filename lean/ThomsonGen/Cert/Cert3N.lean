import ThomsonGen.Cert.NBlk

/-!
# Untyped three-point certificates (`Cert3`) with facially reduced blocks

Upstream's `Cert3.sound` needs every `F`-block and every SOS block to pass `Blk.ok` (an `LDLᵀ` with
nonnegative pivots plus a diagonally dominant remainder).  A sharp certificate lives on a face of the
PSD cone: its blocks are `N · B′ · Nᵀ` with `B′` positive definite and the expanded block singular, so
`Blk.ok` fails for the expanded data.  Here every block of the `Cert3` is the expansion `nb.expand`
(`ThomsonGen/Cert/NBlk.lean`) of a facially reduced witness `nb : NBlk` whose reduced block passes the
fast check (`NBlk.okN`); positivity follows by congruence (`NBlk.fmat_psd_expand`,
`NBlk.sqfE_nonneg_expand`).  The identity check is upstream's `chk cf.idE`, on the expanded data, and
the rest of the soundness proof is upstream's, verbatim up to the positivity inputs.

* `Cert3.FOK b nb`: the kernel block `b` is `nb.expand`, `nb.okN`;
* `Cert3.SOK s nb`: the SOS block `s.B` is `nb.expand`, `nb.okN`, and `nb` has at least `|s.z|` rows
  (`FOK.intro`, `SOK.intro`: for blocks stored as `⟨[], [], X⟩` with a checked `X = nb.expandΔ`);
* `Cert3.soundN`: with `List.Forall₂ FOK cf.F NF`, `List.Forall₂ SOK cf.S NS`, `3 ≤ n`, `0 < Λ`,
  `0 < ad`, `chk cf.idE`, and no cut (`an / ad ≤ -1`):
  `eps / Λ ≤ ∑_{i<j} H(⟪x i, x j⟫)` for all unit vectors `x : Fin n → R3`.

Adapted from huwngtran/thomson-n7-lean @ 25f2fa5, ThomsonN7/Solution.lean (upstream names are
relative to namespace `ThomsonN7`; `ours` ← `upstream`):
* `Cert.sblkE_nonneg_N` ← `Cert.sblkE_nonneg`; `Cert.sos_sum_nonneg_N` ← `Cert.sos_sum_nonneg`;
* `Cert.Cert3.Fm_psd_N` ← the `fmat_psd` step of `Cert.Cert3.sound`;
* `Cert.Cert3.hpt_gramCutN` ← `Cert.Cert3.hpt_gramCut`; `Cert.Cert3.hptN` ← `Cert.Cert3.hpt`
  (with `Cert.Cert3.hpt_cut`); `Cert.Cert3.soundN` ← `Cert.Cert3.sound`.
-/

open Real

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert
open ThreePoint
open scoped RealInnerProductSpace

namespace NBlk

/-- The expansion has one row per row of `N`. -/
lemma length_expandΔ (nb : NBlk) : nb.expandΔ.length = nb.N.length := by
  simp [expandΔ, matMulT, matMul]

/-- A block given by an explicit remainder `X` is the expansion of `nb` once `X = nb.expandΔ`. -/
lemma mk_eq_expand {nb : NBlk} {X : List (List ℤ)} (h : X = nb.expandΔ) :
    (⟨[], [], X⟩ : Blk) = nb.expand := by
  rw [h]
  rfl

end NBlk

lemma exists_of_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil => fun a h => absurd h List.not_mem_nil
  | _, _, .cons hab hl => fun a h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, hab⟩
    · exact exists_of_forall₂ hl a h

namespace Cert3

/-- A kernel block of a `Cert3` is the expansion of a checked facially reduced block. -/
def FOK (b : Blk) (nb : NBlk) : Prop := b = nb.expand ∧ nb.okN = true

/-- An SOS block of a `Cert3` has the expansion of a checked facially reduced block as Gram data. -/
def SOK (s : SBlk) (nb : NBlk) : Prop :=
  s.B = nb.expand ∧ nb.okN = true ∧ s.z.length ≤ nb.N.length

/-- `FOK` for a block given by its expanded remainder `X` (checked: `X = nb.expandΔ`). -/
lemma FOK.intro {nb : NBlk} {X : List (List ℤ)} (hX : X = nb.expandΔ) (hok : nb.okN = true) :
    FOK ⟨[], [], X⟩ nb :=
  ⟨NBlk.mk_eq_expand hX, hok⟩

/-- `SOK` for an SOS block given by its expanded remainder `X` (checked: `X = nb.expandΔ`). -/
lemma SOK.intro {g : List ℕ} {σ : ℕ} {z : List (ℕ × ℕ × ℕ)} {nb : NBlk} {X : List (List ℤ)}
    (hX : X = nb.expandΔ) (hok : nb.okN = true) (hz : z.length ≤ nb.N.length) :
    SOK ⟨g, σ, z, ⟨[], [], X⟩⟩ nb :=
  ⟨NBlk.mk_eq_expand hX, hok, hz⟩

end Cert3

/-- **Positivity by congruence** of an SOS block (mirrors upstream `sblkE_nonneg`). -/
lemma sblkE_nonneg_N (an : ℤ) (ad : ℕ) {s : SBlk} {nb : NBlk} (h : Cert3.SOK s nb) {u v t : ℝ}
    (hg : GramCut an ad u v t) : 0 ≤ (sblkE an ad s).ev u v t := by
  obtain ⟨hB, hok, hz⟩ := h
  have hp := NBlk.okN_parts hok
  rw [sblkE, ev_sbst, ev_mul]
  refine mul_nonneg (gE_nonneg an ad s.g (gramCut_perm3 an ad s.σ hg)) ?_
  rw [hB]
  exact NBlk.sqfE_nonneg_expand ⟨hp.2, hz⟩ rfl rfl hp.1 _ _ _

/-- Mirrors upstream `sos_sum_nonneg`. -/
lemma sos_sum_nonneg_N (an : ℤ) (ad : ℕ) (S : List SBlk) (NS : List NBlk)
    (hS : List.Forall₂ Cert3.SOK S NS) {u v t : ℝ} (hg : GramCut an ad u v t) :
    0 ≤ ((S.map (sblkE an ad)).map fun e => e.ev u v t).sum := by
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨e, ⟨s, hs, rfl⟩, rfl⟩ := hx
  obtain ⟨nb, hnb⟩ := exists_of_forall₂ hS s hs
  exact sblkE_nonneg_N an ad hnb hg

namespace Cert3

/-- The kernel matrices are positive semidefinite (congruence; upstream uses `fmat_psd`). -/
lemma Fm_psd_N (cf : Cert3) (NF : List NBlk) (hF : List.Forall₂ FOK cf.F NF) {k : ℕ}
    (hk : k < cf.K) : (cf.Fm k).PosSemidef := by
  have hmem : cf.blk k ∈ cf.F := by
    unfold Cert3.blk
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  obtain ⟨nb, hb, hok⟩ := exists_of_forall₂ hF _ hmem
  have hp := NBlk.okN_parts hok
  have hm : cf.m k = nb.N.length := by
    unfold Cert3.m
    rw [hb]
    exact NBlk.length_expandΔ nb
  unfold Cert3.Fm
  rw [hb]
  exact NBlk.fmat_psd_expand cf.Lam ⟨hp.2, hm.le⟩ hp.1

/-- The pointwise inequality on Gram triples of the cut (mirrors upstream `hpt_gramCut`). -/
lemma hpt_gramCutN (cf : Cert3) (NS : List NBlk) (hS : List.Forall₂ SOK cf.S NS)
    (hn : 3 ≤ cf.n) (hL : 0 < cf.Lam) (hz : chk cf.idE = true) {u v t : ℝ}
    (hg : GramCut cf.an cf.ad u v t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t)
      ≤ (cf.Hf u + cf.Hf v + cf.Hf t) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) := by
  have hev := chk_sound hz u v t
  simp only [idE, ev_sub, ev_smul, ev_c, ev_hE, ev_ftotE, ev_sumE] at hev
  have hnr : (3 : ℝ) ≤ cf.n := by exact_mod_cast hn
  have hn1 : (cf.n : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (cf.n : ℝ) - 1 := by linarith
    exact this.ne'
  have hLpos : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hC : (0 : ℝ) < (cf.n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hFp : ∑ k ∈ Finset.range cf.K,
        ftotTerm cf.n (fun a b c => (fkE (cf.m k) (cf.blk k) k).ev a b c) u v t
      = 6 * ((cf.n : ℝ) - 1) * cf.Lam
        * ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (key_F (cf.blk k) k cf.n hLpos.ne' hn1 u v t).symm
  rw [hFp] at hev
  push_cast at hev
  rw [Hf_sum]
  exact final_ineq hnr hC hLpos (sos_sum_nonneg_N cf.an cf.ad cf.S NS hS hg) hev

/-- The pointwise inequality required by `three_point_bound` (no cut: `an / ad ≤ -1`; mirrors
upstream `hpt` and `hpt_cut`). -/
lemma hptN (cf : Cert3) (NS : List NBlk) (hS : List.Forall₂ SOK cf.S NS)
    (hn : 3 ≤ cf.n) (hL : 0 < cf.Lam) (hA : 0 < cf.ad) (hz : chk cf.idE = true)
    (hcut : (cf.an : ℝ) / cf.ad ≤ -1) {u v t : ℝ} (hg : GramOK u v t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t)
      ≤ (cf.Hf u + cf.Hf v + cf.Hf t) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) := by
  obtain ⟨hu, hv, ht, hd⟩ := hg
  have hu' := abs_le.1 ((sq_le_one_iff_abs_le_one u).1 hu)
  have hv' := abs_le.1 ((sq_le_one_iff_abs_le_one v).1 hv)
  have ht' := abs_le.1 ((sq_le_one_iff_abs_le_one t).1 ht)
  exact hpt_gramCutN cf NS hS hn hL hz
    (gramCut_of_le hA ⟨hu, hv, ht, hd⟩ (by linarith) (by linarith) (by linarith))

/-- **Soundness of a `Cert3` with facially reduced blocks (no cut).**  Mirrors upstream `sound`:
the `Blk.ok` facts of `check` are replaced by the congruence facts `FOK` / `SOK`. -/
theorem soundN (cf : Cert3) (NF NS : List NBlk) (hF : List.Forall₂ FOK cf.F NF)
    (hS : List.Forall₂ SOK cf.S NS) (hn : 3 ≤ cf.n) (hL : 0 < cf.Lam) (hA : 0 < cf.ad)
    (hz : chk cf.idE = true) (hcut : (cf.an : ℝ) / cf.ad ≤ -1)
    (x : Fin cf.n → R3) (hx : ∀ i, ‖x i‖ = 1) :
    (cf.eps : ℝ) / cf.Lam ≤ ∑ i, ∑ j ∈ Finset.Ioi i, cf.Hf ⟪x i, x j⟫ :=
  three_point_bound hn cf.K cf.m cf.Fm (fun _ hk => Fm_psd_N cf NF hF hk) cf.Hf _
    (fun _ _ _ hg => hptN cf NS hS hn hL hA hz hcut hg) x hx

end Cert3

end Cert
end ThomsonN7
