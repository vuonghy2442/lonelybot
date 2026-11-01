import Orig2.ForkCertBase

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! # Cert_CrossSuit_Part2 - certificate chunks 7..270 (GENERATED)

One of 8 independent slices of the 2308-state certificate; each `decide` is
bounded by its <= 10-state chunk.  Assembled in `Orig2/ForkCertMain.lean`.
-/

namespace Cert

open EqualRung (skey skey_inj allMoves step_mem_allMoves)

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 7.** 10 states. -/
theorem cert_c7 : (c7.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 16.** 10 states. -/
theorem cert_c16 : (c16.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 23.** 10 states. -/
theorem cert_c23 : (c23.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 27.** 4 states. -/
theorem cert_c27 : (c27.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 32.** 10 states. -/
theorem cert_c32 : (c32.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 41.** 4 states. -/
theorem cert_c41 : (c41.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 46.** 10 states. -/
theorem cert_c46 : (c46.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 49.** 10 states. -/
theorem cert_c49 : (c49.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 58.** 10 states. -/
theorem cert_c58 : (c58.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 76.** 4 states. -/
theorem cert_c76 : (c76.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 83.** 10 states. -/
theorem cert_c83 : (c83.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 84.** 2 states. -/
theorem cert_c84 : (c84.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 87.** 10 states. -/
theorem cert_c87 : (c87.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 97.** 10 states. -/
theorem cert_c97 : (c97.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 114.** 6 states. -/
theorem cert_c114 : (c114.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 117.** 10 states. -/
theorem cert_c117 : (c117.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 123.** 10 states. -/
theorem cert_c123 : (c123.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 126.** 4 states. -/
theorem cert_c126 : (c126.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 130.** 4 states. -/
theorem cert_c130 : (c130.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 135.** 10 states. -/
theorem cert_c135 : (c135.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 145.** 10 states. -/
theorem cert_c145 : (c145.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 152.** 10 states. -/
theorem cert_c152 : (c152.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 161.** 10 states. -/
theorem cert_c161 : (c161.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 170.** 10 states. -/
theorem cert_c170 : (c170.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 175.** 10 states. -/
theorem cert_c175 : (c175.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 186.** 4 states. -/
theorem cert_c186 : (c186.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 187.** 10 states. -/
theorem cert_c187 : (c187.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 198.** 10 states. -/
theorem cert_c198 : (c198.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 205.** 10 states. -/
theorem cert_c205 : (c205.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 208.** 10 states. -/
theorem cert_c208 : (c208.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 221.** 10 states. -/
theorem cert_c221 : (c221.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 235.** 2 states. -/
theorem cert_c235 : (c235.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 247.** 6 states. -/
theorem cert_c247 : (c247.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 255.** 6 states. -/
theorem cert_c255 : (c255.map (fun p => p.1)).all certOK = true := by decide

set_option maxHeartbeats 40000000 in
/-- **CERTIFICATE CHUNK 270.** 4 states. -/
theorem cert_c270 : (c270.map (fun p => p.1)).all certOK = true := by decide

end Cert
