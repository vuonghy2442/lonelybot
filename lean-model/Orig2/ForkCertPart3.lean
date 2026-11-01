import Orig2.ForkCertBase

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Cert_CrossSuit_Part3 - certificate chunks 8..265 (GENERATED)

One of 8 independent slices of the 2308-state certificate; each `decide` is
bounded by its <= 10-state chunk.  Assembled in `Orig2/ForkCertMain.lean`.
-/

namespace Cert

open EqualRung (skey skey_inj allMoves step_mem_allMoves)

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 8.** 10 states. -/
theorem cert_c8 : (c8.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 17.** 10 states. -/
theorem cert_c17 : (c17.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 24.** 10 states. -/
theorem cert_c24 : (c24.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 33.** 10 states. -/
theorem cert_c33 : (c33.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 47.** 10 states. -/
theorem cert_c47 : (c47.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 48.** 4 states. -/
theorem cert_c48 : (c48.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 50.** 10 states. -/
theorem cert_c50 : (c50.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 55.** 4 states. -/
theorem cert_c55 : (c55.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 59.** 10 states. -/
theorem cert_c59 : (c59.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 89.** 10 states. -/
theorem cert_c89 : (c89.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 98.** 10 states. -/
theorem cert_c98 : (c98.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 106.** 6 states. -/
theorem cert_c106 : (c106.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 119.** 10 states. -/
theorem cert_c119 : (c119.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 128.** 8 states. -/
theorem cert_c128 : (c128.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 136.** 10 states. -/
theorem cert_c136 : (c136.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 146.** 10 states. -/
theorem cert_c146 : (c146.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 153.** 10 states. -/
theorem cert_c153 : (c153.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 162.** 10 states. -/
theorem cert_c162 : (c162.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 171.** 10 states. -/
theorem cert_c171 : (c171.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 176.** 10 states. -/
theorem cert_c176 : (c176.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 188.** 10 states. -/
theorem cert_c188 : (c188.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 193.** 4 states. -/
theorem cert_c193 : (c193.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 199.** 10 states. -/
theorem cert_c199 : (c199.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 206.** 10 states. -/
theorem cert_c206 : (c206.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 207.** 4 states. -/
theorem cert_c207 : (c207.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 209.** 10 states. -/
theorem cert_c209 : (c209.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 211.** 2 states. -/
theorem cert_c211 : (c211.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 216.** 10 states. -/
theorem cert_c216 : (c216.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 222.** 10 states. -/
theorem cert_c222 : (c222.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 251.** 6 states. -/
theorem cert_c251 : (c251.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 253.** 6 states. -/
theorem cert_c253 : (c253.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 254.** 10 states. -/
theorem cert_c254 : (c254.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 257.** 8 states. -/
theorem cert_c257 : (c257.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 265.** 2 states. -/
theorem cert_c265 : (c265.map (fun p => p.1)).all certOK = true := by decide

end Cert
