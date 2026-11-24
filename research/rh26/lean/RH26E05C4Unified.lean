import RH26E05C1Assembly
import RH26E05C2SmallRamified
import RH26E05C3Exceptional

/-! Cross-module scalar export. Source arithmetic realization is external. -/
namespace RH26E05C4
open scoped BigOperators
noncomputable section

def maskSet (S A : Finset ℕ) : Finset ℕ := S.filter (· ∈ A)
def masked (A : Finset ℕ) (v : ℕ → ℝ) (l : ℕ) : ℝ :=
  if l ∈ A then v l else 0

def priority (A1 A2 A3 A4 A5 : Finset ℕ)
    (v1 v2 v3 v4 v5 : ℕ → ℝ) (l : ℕ) : ℝ :=
  if l ∈ A1 then v1 l else if l ∈ A2 then v2 l else
  if l ∈ A3 then v3 l else if l ∈ A4 then v4 l else
  if l ∈ A5 then v5 l else 0

theorem priority_le_masks (A1 A2 A3 A4 A5 : Finset ℕ)
    (v1 v2 v3 v4 v5 : ℕ → ℝ) (l : ℕ)
    (h1 : 0 ≤ v1 l) (h2 : 0 ≤ v2 l) (h3 : 0 ≤ v3 l)
    (h4 : 0 ≤ v4 l) (h5 : 0 ≤ v5 l) :
    priority A1 A2 A3 A4 A5 v1 v2 v3 v4 v5 l ≤
      masked A1 v1 l + masked A2 v2 l + masked A3 v3 l +
      masked A4 v4 l + masked A5 v5 l := by
  unfold priority masked
  split_ifs <;> linarith

theorem sum_mask (S A : Finset ℕ) (v : ℕ → ℝ) :
    (∑ l ∈ S, masked A v l) = ∑ l ∈ maskSet S A, v l := by
  simp only [maskSet, Finset.sum_filter, masked]

theorem five_mask_majorant (S A1 A2 A3 A4 A5 : Finset ℕ)
    (v1 v2 v3 v4 v5 : ℕ → ℝ) (G0 : ℝ)
    (hn : ∀ l ∈ S, 0 ≤ v1 l ∧ 0 ≤ v2 l ∧ 0 ≤ v3 l ∧ 0 ≤ v4 l ∧ 0 ≤ v5 l) :
    G0 + (∑ l ∈ S, priority A1 A2 A3 A4 A5 v1 v2 v3 v4 v5 l) ≤
      (∑ l ∈ maskSet S A1, v1 l) + (∑ l ∈ maskSet S A2, v2 l) +
      (∑ l ∈ maskSet S A3, v3 l) + (∑ l ∈ maskSet S A4, v4 l) +
      (∑ l ∈ maskSet S A5, v5 l) + G0 := by
  have h := Finset.sum_le_sum (s := S) (fun l hl => by
    obtain ⟨h1,h2,h3,h4,h5⟩ := hn l hl
    exact priority_le_masks A1 A2 A3 A4 A5 v1 v2 v3 v4 v5 l h1 h2 h3 h4 h5)
  simp only [Finset.sum_add_distrib, sum_mask] at h
  linarith only [h]

/-- Raw local supplier data; keep the same C,H,m,b and prime as the export. -/
structure LocalInputs (C H m b l : ℝ) where
  hB : ℝ
  w : ℝ
  Sc : ℝ
  g : ℝ
  eta : ℝ
  band : ℝ
  f : ℝ
  n : ℝ
  t : ℝ
  nV : ℝ
  r : ℝ
  e : ℝ
  flat : ℝ
  bb : ℝ
  len : ℝ
  hB0 : 0 ≤ hB
  hB2 : hB ≤ 2*b
  hlog : Real.logb l hB ≤ H+1
  hw : w ≤ 9*l
  hSc : Sc ≤ 4*H
  hg0 : 0 ≤ g
  hg : g ≤ H
  heta0 : 0 ≤ eta
  heta : eta ≤ 4*H
  hband : band ≤ 1
  hf0 : 0 ≤ f
  hn0 : 0 ≤ n
  ht0 : 0 ≤ t
  hnV0 : 0 ≤ nV
  hr0 : 0 ≤ r
  hf : f ≤ 2*H
  hn : n ≤ H
  ht : t ≤ H
  hnV : nV ≤ 4*H^2
  hr : r ≤ 2*H
  he0 : 0 ≤ e
  he : e ≤ C*(1+hB/l+Real.logb l hB)
  hflat0 : 0 ≤ flat
  hflat : flat ≤ w/l+Sc+g+eta*band
  hbb : bb ≤ C*f*n*t^2*nV*g^2
  hlen : len ≤ (2*f*m+f)*e ∨
    len ≤ 4*f*(C*r*(hB/l^2+flat))+2*f*(C*m*e)

theorem exceptional_local (C H m D s b l : ℝ)
    (hC : 0 ≤ C) (hH : 1 ≤ H) (hm : 2 ≤ m) (hmH : m ≤ H)
    (hD0 : 0 ≤ D) (hD : D ≤ 4*H^7+6*H^4)
    (hs : 0 < s) (hsl : s ≤ l) (hl : 8 ≤ l)
    (hb : 0 ≤ b) (htie : s*D=m*b) (u : LocalInputs C H m b l) :
    u.bb+u.len ≤ 95*(C+1)^2*H^9 := by
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 < l := by linarith
  have hd := RH26E05C3.denominator_envelope H D hH hD
  have hdv := RH26E05C3.exceptional_divisions H m D s l b u.hB
    hH hm hD0 hd hs hsl hl hb u.hB0 u.hB2 htie
  have he := u.he.trans (RH26E05C3.ep_bound H C (u.hB/l) (Real.logb l u.hB)
    hH hC hdv.1 u.hlog)
  have hf := u.hflat.trans (RH26E05C3.flat_bound H l u.w u.Sc u.g u.eta u.band
    hH hl0 u.hw u.hSc u.hg u.heta0 u.heta u.hband)
  have hbb := u.hbb.trans (RH26E05C3.bb_bound H C u.f u.n u.t u.nV u.g
    hH hC u.hf0 u.hn0 u.ht0 u.hnV0 u.hg0 u.hf u.hn u.ht u.hnV u.hg)
  apply RH26E05C3.pointwise_assembly C H u.bb u.len hC hH hbb
  rcases u.hlen with hsplit | hinert
  · exact Or.inl (hsplit.trans (RH26E05C3.split_length H C u.f m u.e
      hH hC u.hf0 hm0 u.he0 u.hf hmH he))
  · have hq : 0 ≤ u.hB/l^2 := div_nonneg u.hB0 (sq_nonneg l)
    exact Or.inr (hinert.trans (RH26E05C3.inert_length H C u.f u.r m
      (u.hB/l^2) u.flat u.e hH hC u.hf0 u.hr0 hm0 hq
      u.hflat0 u.he0 u.hf u.hr hmH hdv.2 hf he))

theorem exceptional_filtered (T : Finset ℕ) (cost : ℕ → ℝ)
    (C H m D s b TT Sc eta t : ℝ)
    (hC : 0 ≤ C) (hH : 2 ≤ H) (hm : 2 ≤ m)
    (hD0 : 0 ≤ D) (hD : D ≤ 4*H^7+6*H^4) (hs : 0 < s)
    (hb : 0 < b) (htie : s*D=m*b)
    (hTT0 : 0 ≤ TT) (hTT : TT ≤ 2*H)
    (hSc0 : 0 ≤ Sc) (hSc : Sc ≤ 4*H)
    (heta0 : 0 ≤ eta) (heta : eta ≤ H) (ht0 : 0 ≤ t) (ht : t ≤ H)
    (hcount : (T.card : ℝ) ≤ (TT+2)*(Sc+3*eta+t+8*b/s+9))
    (hlog : Real.log b ≤ H) (hl : ∀ l ∈ T, 0 < (l : ℝ))
    (htop : ∀ l ∈ T, (l : ℝ) ≤ 3*b)
    (hc0 : ∀ l ∈ T, 0 ≤ cost l)
    (hc : ∀ l ∈ T, cost l ≤ 95*(C+1)^2*H^9) :
    (∑ l ∈ T, Real.log (l : ℝ)*cost l) ≤ 11020*(C+1)^2*H^18 := by
  have hmixed := RH26E05C3.count_mixed_bound H m D s b TT Sc eta t
    (T.card : ℝ) hH hm hD0 hD hs hb.le htie hTT0 hTT hSc0 hSc
    heta0 heta ht0 ht hcount
  have hcard := RH26E05C3.count_envelope H (T.card : ℝ) hH hmixed
  exact RH26E05C3.exceptional_sum T cost C H b hC hH hb hlog hcard hl htop hc0 hc

/-- The six already separated logarithmic suppliers on the generic-small mask. -/
structure SmallInputs (C X Y : ℝ) where
  bb : ℝ
  ep : ℝ
  rb : ℝ
  rc : ℝ
  rd : ℝ
  fl : ℝ
  hY : Y ≤ bb+ep+rb+rc+rd+fl
  hb : bb ≤ C*X
  he : ep ≤ 11*C*(3+2*C)*X
  hrb : rb ≤ 80*C*X
  hrc : rc ≤ 64*C*X
  hrd : rd ≤ 32*C*X
  hf : fl ≤ 4*C*(102+4*(2*C+1)^2)*X

theorem unified_point_bound (S A1 A2 A3 A4 A5 : Finset ℕ)
    (v1 v2 v3 v4 v5 costExc : ℕ → ℝ)
    (q d : ℕ) (C H fm b g y A Q t m D s TT Sc eta : ℝ)
    (X Y G0 : ℝ)
    (hX : X = fm*b*g^2) (hC : 0 ≤ C) (hH : 2 ≤ H)
    (hfm : 1 ≤ fm) (hg : 1 ≤ g) (hb : 1 ≤ b)
    (hscale : 4000000 * RH26E05C1.scale C H ≤ b)
    (hn : ∀ l ∈ S, 0 ≤ v1 l ∧ 0 ≤ v2 l ∧ 0 ≤ v3 l ∧ 0 ≤ v4 l ∧ 0 ≤ v5 l)
    (hY : Y ≤ G0 + ∑ l ∈ S, priority A1 A2 A3 A4 A5 v1 v2 v3 v4 v5 l)
    (hgen : (∑ l ∈ maskSet S A1, v1 l) ≤ 2 * RH26E05C1.scale C H)
    (hglob : G0 ≤ 20 * RH26E05C1.scale C H)
    (hy : 0 ≤ y) (hA : 0 ≤ A) (hLg : (C+3)^2*(1+y)^2 ≤ g) (hAg : A*g ≤ b)
    (hlog23 : (∑ l ∈ maskSet S A2, Real.log (l : ℝ)) ≤ 2*C*y+2)
    (h23 : ∀ l ∈ maskSet S A2,
      v2 l = Real.log (l : ℝ)*(C*fm*b*y+C*A*g^2))
    (hQ : 1 ≤ Q) (hq : 1 ≤ q) (hd : 1 ≤ d) (ht1 : 1 ≤ t)
    (hcond : (Q*(q : ℝ)*(d : ℝ))^36*t^150 ≤ b^(1/2 : ℝ))
    (hlog : Real.log b = g)
    (hqd : ∀ l ∈ maskSet S A3, l=q ∨ l=d)
    (h3 : ∀ l ∈ maskSet S A3, v3 l = Real.log (l : ℝ)*(2*C*fm*b))
    (small : SmallInputs C X (∑ l ∈ maskSet S A4, v4 l))
    (hm : 2 ≤ m) (hmH : m ≤ H)
    (hD0 : 0 ≤ D) (hD : D ≤ 4*H^7+6*H^4) (hs : 0 < s) (htie : s*D=m*b)
    (hTT0 : 0 ≤ TT) (hTT : TT ≤ 2*H) (hSc0 : 0 ≤ Sc) (hSc : Sc ≤ 4*H)
    (heta0 : 0 ≤ eta) (heta : eta ≤ H) (htH : t ≤ H)
    (hcount : ((maskSet S A5).card : ℝ) ≤ (TT+2)*(Sc+3*eta+t+8*b/s+9))
    (hlogH : Real.log b ≤ H)
    (hsl : ∀ l ∈ maskSet S A5, s ≤ (l : ℝ))
    (hl : ∀ l ∈ maskSet S A5, 8 ≤ (l : ℝ))
    (htop : ∀ l ∈ maskSet S A5, (l : ℝ) ≤ 3*b)
    (hc0 : ∀ l ∈ maskSet S A5, 0 ≤ costExc l)
    (hlocal : ∀ l ∈ maskSet S A5, ∃ u : LocalInputs C H m b (l : ℝ),
      costExc l = u.bb+u.len)
    (h5 : ∀ l ∈ maskSet S A5, v5 l = Real.log (l : ℝ)*costExc l) :
    Y ≤ 105*(C+1)^3*X := by
  have hfm0 : 0 ≤ fm := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hgg : 1 ≤ g^2 := by nlinarith only [hg, mul_nonneg hg0 (sub_nonneg.mpr hg)]
  have hbX : b ≤ X := by
    rw [hX]
    calc
      b ≤ fm*b := le_mul_of_one_le_left hb0 hfm
      _ ≤ fm*b*g^2 := le_mul_of_one_le_right (mul_nonneg hfm0 hb0) hgg
  have hX0 : 0 ≤ X := hb0.trans hbX
  have hsmall23 : (∑ l ∈ maskSet S A2, v2 l) ≤ 2*C*X := by
    rw [Finset.sum_congr rfl h23, hX]
    have h := RH26E05C2.row23_assembly (maskSet S A2)
      (fun l => Real.log (l : ℝ)) C fm b y A g hC hy hA hfm hg hLg hAg hlog23
    convert h using 1 <;> ring
  have hram : (∑ l ∈ maskSet S A3, v3 l) ≤ (C/36)*X := by
    rw [Finset.sum_congr rfl h3, hX]
    have h := RH26E05C2.ramified_assembly (maskSet S A3) q d Q t b g C fm
      hQ hq hd ht1 hb hg hC hfm0 hcond hlog hqd
    calc
      _ ≤ (C/36)*fm*b*g := h.1
      _ ≤ (C/36)*fm*b*g^2 := h.2
      _ = _ := by ring
  have hsmall := RH26E05C2.small_assembly C X (∑ l ∈ maskSet S A4, v4 l)
    small.bb small.ep small.rb small.rc small.rd small.fl hC hX0
    small.hY small.hb small.he small.hrb small.hrc small.hrd small.hf
  have hc : ∀ l ∈ maskSet S A5, costExc l ≤ 95*(C+1)^2*H^9 := by
    intro l hmem
    obtain ⟨u, hu⟩ := hlocal l hmem
    rw [hu]
    exact exceptional_local C H m D s b l hC (by linarith) hm hmH
      hD0 hD hs (hsl l hmem) (hl l hmem) hb0 htie u
  have hexc : (∑ l ∈ maskSet S A5, v5 l) ≤ 11020*RH26E05C1.scale C H := by
    rw [Finset.sum_congr rfl h5]
    unfold RH26E05C1.scale
    have h := exceptional_filtered (maskSet S A5) costExc C H m D s b TT Sc eta t
      hC hH hm hD0 hD hs (by linarith) htie hTT0 hTT hSc0 hSc heta0 heta
      (by linarith) htH hcount hlogH (fun l hmem => by linarith [hl l hmem])
      htop hc0 hc
    convert h using 1 <;> ring
  let costs : RH26E05C1.Costs :=
    ⟨∑ l ∈ maskSet S A1, v1 l, ∑ l ∈ maskSet S A2, v2 l,
     ∑ l ∈ maskSet S A3, v3 l, ∑ l ∈ maskSet S A4, v4 l,
     ∑ l ∈ maskSet S A5, v5 l, G0⟩
  have htotal : Y ≤ RH26E05C1.total costs :=
    hY.trans (five_mask_majorant S A1 A2 A3 A4 A5 v1 v2 v3 v4 v5 G0 hn)
  have hbounds : RH26E05C1.RefinedBounds C X H costs :=
    ⟨hgen,hsmall23,hram,hsmall,hexc,hglob⟩
  exact RH26E05C1.refined_assembly C H b X Y costs hC hX0 hscale hbX htotal hbounds

theorem unified_export (C X Y eta R V N : ℝ)
    (hC : 0 ≤ C) (hY : Y ≤ 105*(C+1)^3*X)
    (hEta : eta ≤ R*(Y+V)) (hR : 0 ≤ R) (hN : 0 ≤ N) :
    eta ≤ R*(105*(C+1)^3*(X+N)+V) := by
  exact RH26E05C1.export_propagation eta R Y V (105*(C+1)^3) X N
    hEta hY hR (by positivity) hN

theorem overlap_control :
    priority ∅ ({5} : Finset ℕ) ∅ {5} ∅
      (fun _ => 0) (fun _ => 2) (fun _ => 0) (fun _ => 3) (fun _ => 0) 5 = 2 ∧
    masked ({5} : Finset ℕ) (fun _ => 2) 5 +
      masked ({5} : Finset ℕ) (fun _ => 3) 5 = 5 ∧
    priority ∅ ∅ ∅ ∅ ∅ (fun _ => 1) (fun _ => 2) (fun _ => 3)
      (fun _ => 4) (fun _ => 5) 5 = 0 ∧
    masked ({5} : Finset ℕ) (fun _ => 2) 5 +
      masked ({5} : Finset ℕ) (fun _ => -3) 5 <
      priority ∅ ({5} : Finset ℕ) ∅ {5} ∅
        (fun _ => 0) (fun _ => 2) (fun _ => 0) (fun _ => -3) (fun _ => 0) 5 := by
  norm_num [priority, masked]

end
end RH26E05C4

#print axioms RH26E05C4.priority_le_masks
#print axioms RH26E05C4.sum_mask
#print axioms RH26E05C4.five_mask_majorant
#print axioms RH26E05C4.exceptional_local
#print axioms RH26E05C4.exceptional_filtered
#print axioms RH26E05C4.unified_point_bound
#print axioms RH26E05C4.unified_export
#print axioms RH26E05C4.overlap_control
