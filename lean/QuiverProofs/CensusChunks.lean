import QuiverProofs.CensusData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace QuiverProofs.Census

theorem coverage_chunk_0 : ∀ r : Fin 625, Certificate (0 + r.val) := by decide

theorem coverage_chunk_1 : ∀ r : Fin 625, Certificate (625 + r.val) := by decide

theorem coverage_chunk_2 : ∀ r : Fin 625, Certificate (1250 + r.val) := by decide

theorem coverage_chunk_3 : ∀ r : Fin 625, Certificate (1875 + r.val) := by decide

theorem coverage_chunk_4 : ∀ r : Fin 625, Certificate (2500 + r.val) := by decide

theorem coverage_chunk_5 : ∀ r : Fin 625, Certificate (3125 + r.val) := by decide

theorem coverage_chunk_6 : ∀ r : Fin 625, Certificate (3750 + r.val) := by decide

theorem coverage_chunk_7 : ∀ r : Fin 625, Certificate (4375 + r.val) := by decide

theorem coverage_chunk_8 : ∀ r : Fin 625, Certificate (5000 + r.val) := by decide

theorem coverage_chunk_9 : ∀ r : Fin 625, Certificate (5625 + r.val) := by decide

theorem coverage_chunk_10 : ∀ r : Fin 625, Certificate (6250 + r.val) := by decide

theorem coverage_chunk_11 : ∀ r : Fin 625, Certificate (6875 + r.val) := by decide

theorem coverage_chunk_12 : ∀ r : Fin 625, Certificate (7500 + r.val) := by decide

theorem coverage_chunk_13 : ∀ r : Fin 625, Certificate (8125 + r.val) := by decide

theorem coverage_chunk_14 : ∀ r : Fin 625, Certificate (8750 + r.val) := by decide

theorem coverage_chunk_15 : ∀ r : Fin 625, Certificate (9375 + r.val) := by decide

theorem coverage_chunk_16 : ∀ r : Fin 625, Certificate (10000 + r.val) := by decide

theorem coverage_chunk_17 : ∀ r : Fin 625, Certificate (10625 + r.val) := by decide

theorem coverage_chunk_18 : ∀ r : Fin 625, Certificate (11250 + r.val) := by decide

theorem coverage_chunk_19 : ∀ r : Fin 625, Certificate (11875 + r.val) := by decide

theorem coverage_chunk_20 : ∀ r : Fin 625, Certificate (12500 + r.val) := by decide

theorem coverage_chunk_21 : ∀ r : Fin 625, Certificate (13125 + r.val) := by decide

theorem coverage_chunk_22 : ∀ r : Fin 625, Certificate (13750 + r.val) := by decide

theorem coverage_chunk_23 : ∀ r : Fin 625, Certificate (14375 + r.val) := by decide

theorem coverage_chunk_24 : ∀ r : Fin 625, Certificate (15000 + r.val) := by decide

theorem encoded_census (n : Fin 15625) : Certificate n.val := by
  have hg : n.val / 625 = 0 ∨ n.val / 625 = 1 ∨ n.val / 625 = 2 ∨ n.val / 625 = 3 ∨ n.val / 625 = 4 ∨ n.val / 625 = 5 ∨ n.val / 625 = 6 ∨ n.val / 625 = 7 ∨ n.val / 625 = 8 ∨ n.val / 625 = 9 ∨ n.val / 625 = 10 ∨ n.val / 625 = 11 ∨ n.val / 625 = 12 ∨ n.val / 625 = 13 ∨ n.val / 625 = 14 ∨ n.val / 625 = 15 ∨ n.val / 625 = 16 ∨ n.val / 625 = 17 ∨ n.val / 625 = 18 ∨ n.val / 625 = 19 ∨ n.val / 625 = 20 ∨ n.val / 625 = 21 ∨ n.val / 625 = 22 ∨ n.val / 625 = 23 ∨ n.val / 625 = 24 := by omega
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hc := coverage_chunk_0 ⟨n.val % 625, by omega⟩
    have heq : 0 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_1 ⟨n.val % 625, by omega⟩
    have heq : 625 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_2 ⟨n.val % 625, by omega⟩
    have heq : 1250 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_3 ⟨n.val % 625, by omega⟩
    have heq : 1875 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_4 ⟨n.val % 625, by omega⟩
    have heq : 2500 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_5 ⟨n.val % 625, by omega⟩
    have heq : 3125 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_6 ⟨n.val % 625, by omega⟩
    have heq : 3750 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_7 ⟨n.val % 625, by omega⟩
    have heq : 4375 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_8 ⟨n.val % 625, by omega⟩
    have heq : 5000 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_9 ⟨n.val % 625, by omega⟩
    have heq : 5625 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_10 ⟨n.val % 625, by omega⟩
    have heq : 6250 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_11 ⟨n.val % 625, by omega⟩
    have heq : 6875 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_12 ⟨n.val % 625, by omega⟩
    have heq : 7500 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_13 ⟨n.val % 625, by omega⟩
    have heq : 8125 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_14 ⟨n.val % 625, by omega⟩
    have heq : 8750 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_15 ⟨n.val % 625, by omega⟩
    have heq : 9375 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_16 ⟨n.val % 625, by omega⟩
    have heq : 10000 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_17 ⟨n.val % 625, by omega⟩
    have heq : 10625 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_18 ⟨n.val % 625, by omega⟩
    have heq : 11250 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_19 ⟨n.val % 625, by omega⟩
    have heq : 11875 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_20 ⟨n.val % 625, by omega⟩
    have heq : 12500 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_21 ⟨n.val % 625, by omega⟩
    have heq : 13125 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_22 ⟨n.val % 625, by omega⟩
    have heq : 13750 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_23 ⟨n.val % 625, by omega⟩
    have heq : 14375 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc
  · have hc := coverage_chunk_24 ⟨n.val % 625, by omega⟩
    have heq : 15000 + n.val % 625 = n.val := by omega
    simpa only [heq] using hc

end QuiverProofs.Census
