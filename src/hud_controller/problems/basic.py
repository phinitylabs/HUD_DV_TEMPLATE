import logging

from hud_controller.spec import ProblemSpec, PROBLEM_REGISTRY, HintSpec

logger = logging.getLogger(__name__)


# =============================================================================
# Problem 1: AXI4 Top-Level Testbench + Assertions
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem1_axi4_tb_1",
        description="""Write verif/axi4_top_tb.sv — a SystemVerilog testbench for the axi4_top module.

The DUT is axi4_top (sources/axi4_top.sv), which internally connects axi4_master, axi4_slave, and axi4_interrupt. Instantiate axi4_top, not axi4_slave directly.

The testbench must:

1. Provide clock and reset to the DUT.

2. Drive test stimulus covering:
   - Single-beat writes and reads
   - Multi-beat bursts (INCR, FIXED, WRAP)
   - Multiple address ranges

3. Add SVA assertions to verify:
   - VALID stability: AWVALID, WVALID, ARVALID, BVALID, RVALID must hold until the corresponding READY is seen
   - LAST correctness: WLAST on the final write beat, RLAST on the final read beat
   - Response codes: BRESP and RRESP must be one of 2'b00, 2'b01, 2'b10, 2'b11
   - Ordering: BVALID only after WLAST; RVALID only after ARREADY

4. Use $error("message") for assertion failures, not $display().

To verify your testbench compiles and runs:

    verilator --binary --timing -Wno-fatal \\
        sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv sources/axi4_interrupt.sv \\
        verif/axi4_top_tb.sv --top-module axi4_top_tb -o sim_tb
    ./sim_tb

See docs/Specification.md for AXI4 protocol details and signal descriptions.
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
        description="""Write a SystemVerilog testbench for an AXI4 slave module.

The DUT is axi4_slave_top (sources/), a 5-module AXI4 slave with a 4KB internal memory.

Files to create:
  - verif/axi4_slave_tb.sv
  - verif/sim_main.cpp

The testbench must:

1. Generate a clock and apply a reset sequence.
2. Instantiate axi4_slave_top and connect all AXI4 signals.
3. Implement a write task that drives AWVALID/AWADDR/AWLEN/AWSIZE/AWBURST, then WVALID/WDATA/WSTRB/WLAST, and collects BRESP.
4. Implement a read task that drives ARVALID/ARADDR/ARLEN/ARSIZE/ARBURST and collects RDATA/RRESP/RLAST.
5. Exercise the following scenarios:
   - Single-beat write followed by read with data verification
   - Multi-beat bursts: INCR, FIXED, WRAP
   - Byte strobe variations (partial-word writes)
   - Address boundary conditions
   - Back-to-back transactions
   - Out-of-range address access (expect SLVERR response)

To verify:

    verilator --cc --exe --build --timing -Wno-fatal \\
        sources/axi4_pkg.sv sources/axi4_decoder.sv sources/axi4_memory.sv \\
        sources/axi4_read_channel.sv sources/axi4_write_channel.sv sources/axi4_slave_top.sv \\
        verif/axi4_slave_tb.sv verif/sim_main.cpp --top-module axi4_slave_tb
    ./obj_dir/Vaxi4_slave_tb

See docs/Specification.md for AXI4 protocol details.
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

verif/axi4_slave_tb.sv already has a complete testbench — clock, reset, DUT instantiation, and test stimulus. It compiles and runs correctly but has no assertions.

Add 8-12 SVA assertions in the marked // YOUR TASK section. The assertions should cover:

1. Data integrity: read data must match what was written. Maintain a shadow memory that tracks writes (respecting WSTRB byte lanes) and assert that RDATA equals the shadow value for the same address.

2. WSTRB byte masking: when WSTRB[i] is 0, byte lane i must not change in memory.

3. RLAST timing: RLAST must assert on beat number ARLEN (the final beat), not earlier or later.

4. Response codes: BRESP and RRESP must be valid 2-bit values. Out-of-range addresses must return DECERR (2'b11).

5. ID matching: BID must equal AWID; RID must equal ARID.

Rules:
  - Use property / assert property / disable iff (!aresetn) syntax.
  - Use $error("message") on assertion failures, not $display().
  - Assertions must not fire on the correct (bug-free) design.

File to modify: verif/axi4_slave_tb.sv
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

verif/axi4_slave_tb.sv has a working testbench but no assertions. Add assertions in the marked section covering:

1. Response code validity: BRESP and RRESP must be one of 2'b00, 2'b01, 2'b10, 2'b11.

2. ID matching: BID must equal AWID; RID must equal ARID.

3. LAST signals:
   - BVALID must only assert after WLAST has been seen.
   - RLAST must be set on the final beat of each read burst.

4. Address range: addresses >= 0x00010000 must receive DECERR; valid addresses must not.

5. Handshake completion: BVALID and RVALID must deassert after their respective handshakes complete.

Rules:
  - Use property / assert property / disable iff (!aresetn) syntax.
  - Use $error("message") on assertion failures.
  - Assertions must not fire on the correct design.

File to modify: verif/axi4_slave_tb.sv
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
        description="""Write a testbench for the complete AXI4 system.

The DUT is axi4_top, which instantiates axi4_master, axi4_slave, axi4_interrupt, and axi4_coverage internally. It exposes only clk and resetn ports.

The internal axi4_master automatically generates AXI4 transactions once clock and reset are provided. You do not need to drive AXI signals manually.

Files to create:
  - verif/axi4_top_tb.sv
  - verif/sim_main.cpp

The testbench must:

1. Generate a clock (e.g. 10 ns period).
2. Apply reset: assert low for ~100 ns, then release.
3. Run long enough for the internal master to complete its transactions (~50 us).
4. Call $finish to end simulation.
5. Not use hierarchical references to internal DUT signals. The module only exposes clk and resetn.

To verify:

    verilator --cc --exe --build --timing -Wno-fatal \\
        sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
        sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
        verif/axi4_top_tb.sv verif/sim_main.cpp --top-module axi4_top_tb
    ./obj_dir/Vaxi4_top_tb

See docs/Specification.md for system architecture details.
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

verif/axi4_slave_tb.sv already has one example assertion checking INCR write address increments. The testbench also provides pre-computed tracking signals you can use directly:

  - wr_in_burst, wr_current_addr, wr_prev_addr, wr_addr_incr, wr_beat_count
  - rd_in_burst, rd_current_addr, rd_prev_addr, rd_addr_incr, rd_beat_count
  - wr_burst_type, rd_burst_type (BURST_FIXED=0, BURST_INCR=1, BURST_WRAP=2)

Add at least one more assert property statement in the marked section. Suggestions:

  - WLAST ends a write burst: after wlast fires, wr_in_burst must deassert.
  - INCR read address: rd_current_addr == rd_prev_addr + rd_addr_incr on each INCR beat.

Do not use hierarchical references like dut.u_write_channel.*.

File to modify: verif/axi4_slave_tb.sv
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
        description="""Write a testbench with assertions for the AXI4 interrupt controller.

The DUT is axi4_top. The interrupt controller inside it follows this state machine:
  - IDLE -> PENDING when interrupt_req asserts
  - PENDING -> ACKNOWLEDGED one cycle later
  - ACKNOWLEDGED -> IDLE when interrupt_req deasserts

Files to create:
  - verif/axi4_top_tb.sv
  - verif/sim_main.cpp

The testbench must:

1. Generate a clock (10 ns period) and apply a reset sequence.
2. Drive interrupt_req through these scenarios:
   - Basic: assert req, wait for ack
   - Hold: ack stays high while req stays high
   - Release: ack goes low after req goes low
   - Multiple: successive interrupt cycles
   - Reset: interrupt state clears on reset
3. Add SVA assertions:
   - interrupt_ack only asserts after interrupt_req
   - interrupt_ack appears within 3 cycles of interrupt_req
   - interrupt_ack stays stable while in acknowledged state
   - interrupt_ack deasserts after interrupt_req deasserts

Use only top-level ports (clk, resetn, interrupt_req, interrupt_ack). Do not use hierarchical references.

To verify:

    verilator --cc --exe --build --timing -Wno-fatal \\
        sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
        sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
        verif/axi4_top_tb.sv verif/sim_main.cpp --top-module axi4_top_tb
    ./obj_dir/Vaxi4_top_tb
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
        description="""Write a testbench to verify the AXI4 address decoder.

The DUT is axi4_top, which instantiates master, slave, interrupt, and coverage internally. The address decoder inside the slave behaves as follows:
  - Valid range 0x0000-0x0FFF (4 KB): returns OKAY (2'b00)
  - Out-of-range address >= 0x1000: returns SLVERR (2'b10)

Files to create:
  - verif/axi4_top_tb.sv
  - verif/sim_main.cpp

The testbench must:

1. Generate a clock and apply a reset sequence.
2. Issue write and read transactions to:
   - Valid addresses in range (e.g. 0x0000, 0x0100, 0x0FFC)
   - Out-of-range addresses (e.g. 0x1000, 0x2000, 0xFFFF)
   - The boundary address 0x0FFF (last valid)
3. Verify:
   - BRESP == OKAY for in-range writes
   - RRESP == OKAY for in-range reads
   - BRESP == SLVERR for out-of-range writes
   - RRESP == SLVERR for out-of-range reads
4. Use $error("message") to report any mismatch.

To verify:

    verilator --binary --timing -Wno-fatal \\
        sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
        sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
        verif/axi4_top_tb.sv --top-module axi4_top_tb -o sim_tb
    ./sim_tb
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

verif/axi4_top_tb.sv has a working testbench that drives the axi4_top module. It compiles and runs but has no assertions about memory correctness or protocol behavior.

Add SVA assertions in the marked section covering:

1. Write-then-read data integrity: data read back from an address must match what was last written there, accounting for WSTRB byte masking.

2. VALID stability:
   - Once AWVALID asserts, it must stay high until AWREADY.
   - Once WVALID asserts, it must stay high until WREADY.
   - Once ARVALID asserts, it must stay high until ARREADY.

3. LAST correctness:
   - WLAST must assert on the final write data beat.
   - RLAST must assert on the final read data beat.

4. Response code validity: BRESP and RRESP must be one of 2'b00, 2'b01, 2'b10, 2'b11.

Rules:
  - Use property / assert property / disable iff (!aresetn) syntax.
  - Use $error("message") on failures.
  - Assertions must not fire on the correct design.

File to modify: verif/axi4_top_tb.sv
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
        description="""Write a testbench with read-channel assertions for the AXI4 system.

The DUT is axi4_top, which internally connects master, slave, interrupt, and coverage.

Files to create:
  - verif/axi4_top_tb.sv
  - verif/sim_main.cpp

The testbench must:

1. Generate a clock and apply a reset sequence.
2. Write known data to several addresses, then read it back and verify RDATA matches.
3. Exercise read bursts:
   - Single-beat reads (ARLEN=0)
   - Multi-beat INCR bursts (ARLEN=3, ARLEN=7)
4. Add SVA assertions:
   - RLAST asserts exactly on the final read beat (beat index == ARLEN)
   - RDATA matches previously written data for in-range addresses
   - ARVALID holds until ARREADY
   - RRESP is a valid response code (OKAY or SLVERR for this slave)
5. Use $error("message") on assertion failures.

To verify:

    verilator --binary --timing -Wno-fatal \\
        sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv \\
        sources/axi4_interrupt.sv sources/axi4_coverage.sv \\
        verif/axi4_top_tb.sv --top-module axi4_top_tb -o sim_tb
    ./sim_tb

See docs/Specification.md for AXI4 signal descriptions.
""",
        difficulty="hard",
        base="Problem10_axi4_read_tb_sva_baseline",
        test="Problem10_axi4_read_tb_sva_test",
        golden="Problem10_axi4_read_tb_sva_golden",
        test_files=["tests/test_Problem10_axi4_read_tb_sva_hidden.py"],
    )
)
