import logging

from hud_controller.spec import ProblemSpec, PROBLEM_REGISTRY, HintSpec

logger = logging.getLogger(__name__)


# =============================================================================
# Problem 1: AXI4 Top-Level Testbench + Assertions
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem1_axi4_tb_1",
        description="""Create a SystemVerilog testbench for the AXI4 top-level module.

**Your Task**: Write `verif/axi4_top_tb.sv` that instantiates and exercises `axi4_top`.

**DUT**: `axi4_top` (in `sources/axi4_top.sv`) — connects `axi4_master`, `axi4_slave`, and `axi4_interrupt` internally. Instantiate `axi4_top`, not `axi4_slave` directly.

**Requirements**:

1. Provide clock and reset signals to the DUT.

2. Add SVA assertions to verify:
   - VALID stability: AWVALID, WVALID, ARVALID, BVALID, RVALID must hold until the corresponding READY is seen
   - LAST correctness: WLAST on the final write beat, RLAST on the final read beat
   - Response codes: BRESP and RRESP must be 2'b00, 2'b01, 2'b10, or 2'b11
   - Ordering: BVALID only after WLAST; RVALID only after ARREADY

3. Drive test stimulus:
   - Single-beat writes and reads
   - Multi-beat bursts (INCR, FIXED, WRAP)
   - Multiple address ranges

4. Use `$error("message")` for assertion failures, not `$display()`.

**Verification** (must pass before submitting):
```bash
verilator --binary --timing -Wno-fatal \\
    sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv sources/axi4_interrupt.sv \\
    verif/axi4_top_tb.sv --top-module axi4_top_tb -o sim_tb
./sim_tb
```

See `docs/Specification.md` for AXI4 protocol details and signal descriptions.
""",
        difficulty="medium",
        base="Problem1_axi4_tb_1_baseline",
        test="Problem1_axi4_tb_1_test",
        golden="Problem1_axi4_tb_1_golden",
        test_files=["tests/test_Problem1_axi4_tb_1_hidden.py"],
    )
)


# =============================================================================
# Problem 2: AXI4 Slave Testbench
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem2_axi4_tb_1",
        description="""Create a SystemVerilog testbench for an AXI4 slave module.

**Your Task**: Write a testbench that drives and verifies the AXI4 slave.

**Files to create**:
- `verif/axi4_slave_tb.sv` — SystemVerilog testbench
- `verif/sim_main.cpp` — Verilator C++ wrapper

**DUT**: `axi4_slave_top` (in `sources/`) — a 5-module AXI4 slave with a 4KB memory.

**Requirements**:

1. Clock generation and reset sequence.
2. DUT instantiation (`axi4_slave_top`).
3. AXI4 write task: drive AWVALID/AWADDR/AWLEN/AWSIZE/AWBURST, then WVALID/WDATA/WSTRB/WLAST, collect BRESP.
4. AXI4 read task: drive ARVALID/ARADDR/ARLEN/ARSIZE/ARBURST, collect RDATA/RRESP/RLAST.
5. Test scenarios:
   - Single-beat write and read with data verification
   - Multi-beat bursts: INCR, FIXED, WRAP
   - Byte strobe variations
   - Address boundary conditions
   - Back-to-back transactions
   - Out-of-range address (expect SLVERR)

**Verification**:
```bash
verilator --cc --exe --build --timing -Wno-fatal \\
    sources/axi4_pkg.sv sources/axi4_decoder.sv sources/axi4_memory.sv \\
    sources/axi4_read_channel.sv sources/axi4_write_channel.sv sources/axi4_slave_top.sv \\
    verif/axi4_slave_tb.sv verif/sim_main.cpp --top-module axi4_slave_tb
./obj_dir/Vaxi4_slave_tb
```

See `docs/Specification.md` for AXI4 protocol details.
""",
        difficulty="hard",
        base="Problem2_axi4_tb_1_baseline",
        test="Problem2_axi4_tb_1_test",
        golden="Problem2_axi4_tb_1_golden",
        test_files=["tests/test_Problem2_axi4_tb_1_hidden.py"],
    )
)


# =============================================================================
# Problem 3: AXI4 Slave SVA Assertions
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem3_axi4_sva_1",
        description="""Add SVA assertions to an existing AXI4 slave testbench.

**Context**: `verif/axi4_slave_tb.sv` already contains a complete testbench with clock, reset, DUT instantiation, and test stimulus. It compiles and runs correctly but has no assertions.

**Your Task**: Add 8–12 SVA assertions in the marked `// YOUR TASK` section of `verif/axi4_slave_tb.sv`.

**What to assert**:

1. **Data integrity** — read data must match what was written:
   - Maintain a shadow memory that tracks writes (respecting WSTRB byte lanes)
   - Assert that RDATA equals the shadow memory value for the same address

2. **WSTRB byte masking** — when WSTRB[i] is 0, byte lane i must not change

3. **RLAST timing** — RLAST must assert on beat number ARLEN (the final beat), not earlier or later

4. **Response codes** — BRESP and RRESP must be valid 2-bit values; out-of-range addresses must return DECERR (2'b11)

5. **ID matching** — BID must equal AWID; RID must equal ARID

**Rules**:
- Use `property` / `assert property` / `disable iff (!aresetn)` syntax
- Use `$error("message")` on assertion failures — not `$display()`
- Assertions must NOT fire on the correct (bug-free) design

**File to modify**: `verif/axi4_slave_tb.sv`
""",
        difficulty="medium",
        base="Problem3_axi4_sva_1_baseline",
        test="Problem3_axi4_sva_1_test",
        golden="Problem3_axi4_sva_1_golden",
        test_files=["tests/test_Problem3_axi4_sva_1_hidden.py"],
    )
)


# =============================================================================
# Problem 4: AXI4 Slave Protocol SVA Assertions
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem4_axi4_slave_sva",
        description="""Add SVA assertions to verify AXI4 slave protocol compliance.

**Context**: `verif/axi4_slave_tb.sv` has a working testbench but no assertions.

**Your Task**: Add SVA assertions in the marked section of `verif/axi4_slave_tb.sv`.

**What to assert**:

1. **Response code validity** — BRESP and RRESP must be 2'b00, 2'b01, 2'b10, or 2'b11

2. **ID matching** — BID must equal AWID; RID must equal ARID

3. **LAST signals**:
   - BVALID must only assert after WLAST has been seen
   - RLAST must be set on the final beat of each read burst

4. **Address range** — addresses >= 0x00010000 must receive DECERR; valid addresses must not

5. **Handshake completion** — BVALID and RVALID must deassert after their respective handshakes complete

**Rules**:
- Use `property` / `assert property` / `disable iff (!aresetn)` syntax
- Use `$error("message")` on assertion failures
- Assertions must not fire on the correct design

**File to modify**: `verif/axi4_slave_tb.sv`
""",
        difficulty="medium",
        base="Problem4_axi4_slave_sva_baseline",
        test="Problem4_axi4_slave_sva_test",
        golden="Problem4_axi4_slave_sva_golden",
        test_files=["tests/test_Problem4_axi4_slave_sva_hidden.py"],
    )
)


# =============================================================================
# Problem 5: AXI4 Top-Level System Testbench
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem5_axi4_top_tb",
        description="""Create a testbench for the complete AXI4 system.

**Your Task**: Write a testbench that drives the `axi4_top` module.

**Files to create**:
- `verif/axi4_top_tb.sv` — SystemVerilog testbench
- `verif/sim_main.cpp` — Verilator C++ wrapper

**DUT**: `axi4_top` — top-level module that instantiates `axi4_master`, `axi4_slave`, `axi4_interrupt`, and `axi4_coverage` internally. It exposes only `clk` and `resetn` ports.

**How it works**: The internal `axi4_master` automatically generates AXI4 transactions when clock and reset are provided. You do not need to drive AXI signals manually.

**Requirements**:
1. Generate a clock (e.g., 10 ns period).
2. Apply reset: assert low for ~100 ns, then release.
3. Run simulation long enough for the internal master to complete its transactions (~50 µs).
4. Call `$finish` to end simulation.
5. Do NOT use hierarchical references to access internal DUT signals (e.g., `dut.axi_awaddr` is illegal — the module only exposes `clk` and `resetn`).

**Verification**:
```bash
verilator --cc --exe --build --timing -Wno-fatal \\
    sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
    sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
    verif/axi4_top_tb.sv verif/sim_main.cpp --top-module axi4_top_tb
./obj_dir/Vaxi4_top_tb
```

See `docs/Specification.md` for system architecture details.
""",
        difficulty="hard",
        base="Problem5_axi4_top_tb_baseline",
        test="Problem5_axi4_top_tb_test",
        golden="Problem5_axi4_top_tb_golden",
        test_files=["tests/test_Problem5_axi4_top_tb_hidden.py"],
    )
)


# =============================================================================
# Problem 6: AXI4 Burst Address SVA
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem6_axi4_burst_sva",
        description="""Add an SVA assertion to verify AXI4 burst address behavior.

**Context**: `verif/axi4_slave_tb.sv` already has one example assertion checking INCR write address increments. The testbench also provides pre-computed tracking signals you can use directly.

**Your Task**: Add at least one more `assert property` statement in the marked section.

**Available tracking signals** (already declared in the testbench):
- `wr_in_burst`, `wr_current_addr`, `wr_prev_addr`, `wr_addr_incr`, `wr_beat_count`
- `rd_in_burst`, `rd_current_addr`, `rd_prev_addr`, `rd_addr_incr`, `rd_beat_count`
- `wr_burst_type`, `rd_burst_type` (BURST_FIXED=0, BURST_INCR=1, BURST_WRAP=2)

**Suggested assertions** (choose one or more):
- WLAST ends a write burst: after `wlast` fires, `wr_in_burst` must deassert
- INCR read address: `rd_current_addr == rd_prev_addr + rd_addr_incr` on each INCR beat

**Do not** use hierarchical references like `dut.u_write_channel.*`.

**File to modify**: `verif/axi4_slave_tb.sv`
""",
        difficulty="easy",
        base="Problem6_axi4_burst_sva_baseline",
        test="Problem6_axi4_burst_sva_test",
        golden="Problem6_axi4_burst_sva_golden",
        test_files=["tests/test_Problem6_axi4_burst_sva_hidden.py"],
    )
)


# =============================================================================
# Problem 7: AXI4 Interrupt Controller Testbench + Assertions
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem7_axi4_interrupt_tb",
        description="""Create a testbench with assertions for the AXI4 interrupt controller.

**Your Task**: Write `verif/axi4_top_tb.sv` that exercises and verifies the interrupt controller inside `axi4_top`.

**Files to create**:
- `verif/axi4_top_tb.sv`
- `verif/sim_main.cpp`

**Interrupt controller behavior**:
- IDLE → PENDING when `interrupt_req` asserts
- PENDING → ACKNOWLEDGED one cycle later
- ACKNOWLEDGED → IDLE when `interrupt_req` deasserts

**Requirements**:

1. Clock generation (10 ns period) and reset sequence.
2. Drive `interrupt_req` through the following test sequences:
   - Basic: assert req, wait for ack
   - Hold: ack stays high while req stays high
   - Release: ack goes low after req goes low
   - Multiple: successive interrupt cycles
   - Reset: interrupt state clears on reset
3. Add SVA assertions:
   - `interrupt_ack` only asserts after `interrupt_req`
   - `interrupt_ack` appears within 3 cycles of `interrupt_req`
   - `interrupt_ack` stays stable while in acknowledged state
   - `interrupt_ack` deasserts after `interrupt_req` deasserts

**Rule**: Use only top-level ports (`clk`, `resetn`, `interrupt_req`, `interrupt_ack`). Do not use hierarchical references.

**Verification**:
```bash
verilator --cc --exe --build --timing -Wno-fatal \\
    sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
    sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
    verif/axi4_top_tb.sv verif/sim_main.cpp --top-module axi4_top_tb
./obj_dir/Vaxi4_top_tb
```
""",
        difficulty="hard",
        base="Problem7_axi4_interrupt_tb_baseline",
        test="Problem7_axi4_interrupt_tb_test",
        golden="Problem7_axi4_interrupt_tb_golden",
        test_files=["tests/test_Problem7_axi4_interrupt_tb_hidden.py"],
    )
)


# =============================================================================
# Problem 8: AXI4 Decoder Testbench
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem8_axi4_decoder_tb",
        description="""Create a testbench to verify the AXI4 address decoder.

**Your Task**: Write `verif/axi4_top_tb.sv` that exercises address decoding behavior.

**Files to create**:
- `verif/axi4_top_tb.sv`
- `verif/sim_main.cpp`

**DUT**: `axi4_top` (instantiates master, slave, interrupt, coverage internally).

**Address decoder behavior**:
- Valid range: 0x0000–0x0FFF (4 KB) → OKAY (2'b00)
- Out of range: address >= 0x1000 → SLVERR (2'b10)

**Requirements**:

1. Clock generation and reset sequence.
2. Write and read transactions covering:
   - Valid addresses in range (0x0000, 0x0100, 0x0FFC)
   - Out-of-range addresses (0x1000, 0x2000, 0xFFFF)
   - Boundary address (0x0FFF — last valid)
3. Verify:
   - BRESP == OKAY for in-range writes
   - RRESP == OKAY for in-range reads
   - BRESP == SLVERR for out-of-range writes
   - RRESP == SLVERR for out-of-range reads
4. Use `$error("message")` to report any mismatch.

**Verification**:
```bash
verilator --binary --timing -Wno-fatal \\
    sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
    sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
    verif/axi4_top_tb.sv --top-module axi4_top_tb -o sim_tb
./sim_tb
```
""",
        difficulty="medium",
        base="Problem8_axi4_decoder_tb_baseline",
        test="Problem8_axi4_decoder_tb_test",
        golden="Problem8_axi4_decoder_tb_golden",
        test_files=["tests/test_Problem8_axi4_decoder_tb_hidden.py"],
    )
)


# =============================================================================
# Problem 9: AXI4 Memory SVA Assertions
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem9_axi4_memory_sva",
        description="""Add SVA assertions to verify AXI4 slave memory behavior.

**Context**: `verif/axi4_top_tb.sv` has a working testbench that drives the `axi4_top` module. It compiles and runs but lacks assertions about memory correctness.

**Your Task**: Add SVA assertions in the marked section.

**What to assert**:

1. **Write-then-read data integrity**: data read back from an address must match what was last written there (accounting for WSTRB byte masking)

2. **VALID stability**:
   - Once AWVALID asserts, it must stay high until AWREADY
   - Once WVALID asserts, it must stay high until WREADY
   - Once ARVALID asserts, it must stay high until ARREADY

3. **LAST correctness**:
   - WLAST must assert on the final write data beat
   - RLAST must assert on the final read data beat

4. **Response code validity**: BRESP and RRESP must be 2'b00, 2'b01, 2'b10, or 2'b11

**Rules**:
- Use `property` / `assert property` / `disable iff (!aresetn)`
- Use `$error("message")` on failures
- Assertions must not fire on the correct design

**File to modify**: `verif/axi4_top_tb.sv`
""",
        difficulty="medium",
        base="Problem9_axi4_memory_sva_baseline",
        test="Problem9_axi4_memory_sva_test",
        golden="Problem9_axi4_memory_sva_golden",
        test_files=["tests/test_Problem9_axi4_memory_sva_hidden.py"],
    )
)


# =============================================================================
# Problem 10: AXI4 Read Channel Testbench + SVA
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem10_axi4_read_tb_sva",
        description="""Create a testbench with read-channel assertions for the AXI4 system.

**Your Task**: Write `verif/axi4_top_tb.sv` that exercises the read channel and adds assertions.

**Files to create**:
- `verif/axi4_top_tb.sv`
- `verif/sim_main.cpp`

**DUT**: `axi4_top` (master, slave, interrupt, coverage connected internally).

**Requirements**:

1. Clock generation and reset.
2. Write known data to several addresses, then read it back — verify RDATA matches.
3. Exercise read bursts:
   - Single-beat reads (ARLEN=0)
   - Multi-beat INCR bursts (ARLEN=3, ARLEN=7)
4. Add SVA assertions:
   - RLAST asserts exactly on the final read beat (beat index == ARLEN)
   - RDATA matches previously written data for in-range addresses
   - ARVALID holds until ARREADY
   - RRESP is valid (00 or 10 for this slave)
5. Use `$error("message")` on assertion failures.

**Verification**:
```bash
verilator --binary --timing -Wno-fatal \\
    sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
    sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
    verif/axi4_top_tb.sv --top-module axi4_top_tb -o sim_tb
./sim_tb
```

See `docs/Specification.md` for AXI4 signal descriptions.
""",
        difficulty="hard",
        base="Problem10_axi4_read_tb_sva_baseline",
        test="Problem10_axi4_read_tb_sva_test",
        golden="Problem10_axi4_read_tb_sva_golden",
        test_files=["tests/test_Problem10_axi4_read_tb_sva_hidden.py"],
    )
)
