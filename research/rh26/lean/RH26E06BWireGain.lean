import Mathlib

/-! Exact scalar transport in the B19/B20 wire. Surrounding family
witnesses are held fixed; no arithmetic realization is asserted. -/
namespace RH26E06B

noncomputable section

def ce (C Ce cD C0 : ℝ) : ℝ := max C0 (2*C+Ce+cD+3)
def wire (C Ce cD C0 : ℝ) : ℝ :=
  max 0 (max (50*C0+10) (60*ce C Ce cD C0))
def threshold (B C Ce cD C0 : ℝ) : ℝ :=
  max B (272+2*ce C Ce cD C0)

theorem wire_collapse (C Ce cD C0 : ℝ) (h0 : 28 ≤ C0) :
    wire C Ce cD C0 = 60*ce C Ce cD C0 := by
  have hE : C0 ≤ ce C Ce cD C0 := le_max_left _ _
  have h1 : 50*C0+10 ≤ 60*ce C Ce cD C0 := by linarith
  have h2 : 0 ≤ 60*ce C Ce cD C0 := by linarith
  unfold wire
  rw [max_eq_right h1, max_eq_right h2]

theorem ce_mono (C lo hi cD C0 : ℝ) (h : lo ≤ hi) :
    ce C lo cD C0 ≤ ce C hi cD C0 := by
  unfold ce
  exact max_le_max le_rfl (by linarith)

theorem ce_gain_bounds (C lo hi cD C0 : ℝ) (h : lo ≤ hi) :
    0 ≤ ce C hi cD C0-ce C lo cD C0 ∧
    ce C hi cD C0-ce C lo cD C0 ≤ hi-lo := by
  have hm := ce_mono C lo hi cD C0 h
  have h1 : C0 ≤ ce C lo cD C0 := le_max_left _ _
  have h2 : 2*C+lo+cD+3 ≤ ce C lo cD C0 := le_max_right _ _
  have hc : ce C hi cD C0 ≤ ce C lo cD C0+(hi-lo) := by
    change max C0 (2*C+hi+cD+3) ≤ _
    exact max_le (by linarith) (by linarith)
  exact ⟨by linarith only [hm], by linarith only [hc]⟩

theorem wire_gain_identity (C lo hi cD C0 : ℝ) (h0 : 28 ≤ C0) :
    wire C hi cD C0-wire C lo cD C0 =
      60*(max (hi-(C0-(2*C+cD+3))) 0-max (lo-(C0-(2*C+cD+3))) 0) := by
  have hid (a : ℝ) : ce C a cD C0 =
      C0+max (a-(C0-(2*C+cD+3))) 0 := by
    unfold ce
    by_cases h : C0 ≤ 2*C+a+cD+3
    · rw [max_eq_right h, max_eq_left (show 0 ≤ a-(C0-(2*C+cD+3)) by linarith)]
      ring
    · have h' : 2*C+a+cD+3 ≤ C0 := le_of_lt (lt_of_not_ge h)
      rw [max_eq_left h', max_eq_right (show a-(C0-(2*C+cD+3)) ≤ 0 by linarith)]
      ring
  rw [wire_collapse C hi cD C0 h0, wire_collapse C lo cD C0 h0, hid hi, hid lo]
  ring

theorem wire_gain_bounds (C lo hi cD C0 : ℝ) (h0 : 28 ≤ C0) (h : lo ≤ hi) :
    0 ≤ wire C hi cD C0-wire C lo cD C0 ∧
    wire C hi cD C0-wire C lo cD C0 ≤ 60*(hi-lo) := by
  rw [wire_collapse C hi cD C0 h0, wire_collapse C lo cD C0 h0]
  obtain ⟨ha,hb⟩ := ce_gain_bounds C lo hi cD C0 h
  exact ⟨by linarith only [ha], by linarith only [hb]⟩

theorem full_wire_gain (C lo hi cD C0 : ℝ) (h0 : 28 ≤ C0) (h : lo ≤ hi)
    (hactive : C0 ≤ 2*C+lo+cD+3) :
    wire C hi cD C0-wire C lo cD C0 = 60*(hi-lo) := by
  rw [wire_collapse C hi cD C0 h0, wire_collapse C lo cD C0 h0]
  unfold ce
  rw [max_eq_right (show C0 ≤ 2*C+hi+cD+3 by linarith), max_eq_right hactive]
  ring

theorem zero_wire_gain (C lo hi cD C0 : ℝ) (h0 : 28 ≤ C0) (h : lo ≤ hi)
    (hinactive : 2*C+hi+cD+3 ≤ C0) :
    wire C hi cD C0 = wire C lo cD C0 := by
  rw [wire_collapse C hi cD C0 h0, wire_collapse C lo cD C0 h0]
  unfold ce
  rw [max_eq_left hinactive, max_eq_left (show 2*C+lo+cD+3 ≤ C0 by linarith)]

theorem threshold_gain_bounds (B C lo hi cD C0 : ℝ) (h : lo ≤ hi) :
    0 ≤ threshold B C hi cD C0-threshold B C lo cD C0 ∧
    threshold B C hi cD C0-threshold B C lo cD C0 ≤
      2*(ce C hi cD C0-ce C lo cD C0) ∧
    threshold B C hi cD C0-threshold B C lo cD C0 ≤ 2*(hi-lo) := by
  obtain ⟨ha,hb⟩ := ce_gain_bounds C lo hi cD C0 h
  have hm : threshold B C lo cD C0 ≤ threshold B C hi cD C0 := by
    unfold threshold
    exact max_le_max le_rfl (by linarith only [ha])
  have h1 : B ≤ threshold B C lo cD C0 := le_max_left _ _
  have h2 : 272+2*ce C lo cD C0 ≤ threshold B C lo cD C0 := le_max_right _ _
  have hc : threshold B C hi cD C0 ≤ threshold B C lo cD C0+
      2*(ce C hi cD C0-ce C lo cD C0) := by
    change max B (272+2*ce C hi cD C0) ≤ _
    exact max_le (by linarith only [h1,ha]) (by linarith only [h2])
  exact ⟨by linarith only [hm], by linarith only [hc], by linarith only [hc,hb]⟩

theorem refined_source_gain (Ca C cD C0 : ℝ) (hCa : 0 ≤ Ca) (h0 : 28 ≤ C0) :
    let hi := 2000*(Ca+1)^3+1
    let lo := 105*(Ca+1)^3+1
    0 ≤ wire C hi cD C0-wire C lo cD C0 ∧
    wire C hi cD C0-wire C lo cD C0 ≤ 113700*(Ca+1)^3 ∧
    (C0 ≤ 2*C+lo+cD+3 →
      wire C hi cD C0-wire C lo cD C0 = 113700*(Ca+1)^3) := by
  dsimp
  have hp : 0 ≤ (Ca+1)^3 := pow_nonneg (by linarith) 3
  have h : 105*(Ca+1)^3+1 ≤ 2000*(Ca+1)^3+1 := by linarith only [hp]
  obtain ⟨ha,hb⟩ := wire_gain_bounds C (105*(Ca+1)^3+1) (2000*(Ca+1)^3+1) cD C0 h0 h
  refine ⟨ha, by linarith only [hb], ?_⟩
  intro hactive
  rw [full_wire_gain C (105*(Ca+1)^3+1) (2000*(Ca+1)^3+1) cD C0 h0 h hactive]
  ring

theorem floor_controls :
    wire 0 100 2 100-wire 0 1 2 100 = 300 ∧
    (60:ℝ)*(100-1) = 5940 ∧
    wire 0 100 2 28-wire 0 40 2 28 = 3600 ∧
    threshold 1000 0 100 2 28 = threshold 1000 0 40 2 28 := by
  norm_num [wire, ce, threshold, max_def]

end
end RH26E06B

#print axioms RH26E06B.wire_collapse
#print axioms RH26E06B.ce_mono
#print axioms RH26E06B.ce_gain_bounds
#print axioms RH26E06B.wire_gain_identity
#print axioms RH26E06B.wire_gain_bounds
#print axioms RH26E06B.full_wire_gain
#print axioms RH26E06B.zero_wire_gain
#print axioms RH26E06B.threshold_gain_bounds
#print axioms RH26E06B.refined_source_gain
#print axioms RH26E06B.floor_controls
