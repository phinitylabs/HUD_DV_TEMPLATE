import logging

from hud_controller.spec import ProblemSpec, PROBLEM_REGISTRY, HintSpec

logger = logging.getLogger(__name__)


PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem1_axi4_tb_1",
        description="""Create a SystemVerilog testbench for the AXI4 slave module with assertions.

**Task**: Write a comprehensive testbench that verifies the AXI4 slave module behavior.

**Requirements**:

1. **Create Testbench File**: `verif/axi4_top_tb.sv`
   - Instantiate the DUT from `sources/axi4_top.sv` (NOT axi4_slave directly!)
   - The axi4_top module internally connects axi4_master, axi4_slave, and axi4_interrupt
   - Your testbench monitors the internal AXI signals between master and slave
   - Provide clock and reset signals
   - Include `$finish;` statement

2. **Add Protocol Assertions** to verify:
   
   a. **VALID Signal Stability**:
      - AWVALID must remain stable until AWREADY
      - WVALID must remain stable until WREADY
      - ARVALID must remain stable until ARREADY
      - BVALID must remain stable until BREADY
      - RVALID must remain stable until RREADY
   
   b. **LAST Signal Correctness**:
      - WLAST must be asserted on the final write data beat
      - RLAST must be asserted on the final read data beat
   
   c. **Response Code Validation**:
      - BRESP must be valid (00=OKAY, 01=EXOKAY, 10=SLVERR, 11=DECERR)
      - RRESP must be valid (00=OKAY, 01=EXOKAY, 10=SLVERR, 11=DECERR)
   
   d. **Timing Relationships**:
      - Write response (BVALID) must follow write data completion (WLAST)
      - Read data (RVALID) must follow read address acceptance (ARREADY)

3. **Provide Test Stimulus**:
   - Single-beat write transactions
   - Multi-beat burst writes (INCR, FIXED, WRAP)
   - Read transactions with various burst lengths
   - Different address ranges

4. **Testbench Quality**:
   - Must compile AND simulate successfully with Verilator
   - Use `$display("ASSERTION PASSED: ...")` and `$display("ASSERTION FAILED: ...")` for assertion reporting

**Verification Command** (MUST pass before submission):
```bash
# Compile for simulation (NOT just lint-only!)
verilator --binary --timing -Wno-fatal \\
    sources/axi4_top.sv sources/axi4_master.sv sources/axi4_slave.sv sources/axi4_interrupt.sv \\
    verif/axi4_top_tb.sv --top-module axi4_top_tb -o sim_tb

# Run simulation
./sim_tb
```

**IMPORTANT**: 
- `verilator --lint-only` is NOT sufficient! You MUST test with `--binary` and run the simulation.
- The testbench MUST instantiate `axi4_top` (not `axi4_slave` directly).
- All DUT source files must be included in compilation.

**Files to Create**:
- `verif/axi4_top_tb.sv` (new file - agent creates this)

**Simulator**: Verilator with --timing flag (SystemVerilog timing delays supported)

See `docs/Specification.md` for AXI4 protocol details.
""",
        difficulty="medium",
        base="Problem1_axi4_tb_1_baseline",
        test="Problem1_axi4_tb_1_test",
        golden="Problem1_axi4_tb_1_golden",
        test_files=["tests/test_Problem1_axi4_tb_1_hidden.py"],
    )
)

PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem2_axi4_tb_1",
        description="""Create a comprehensive SystemVerilog testbench for an AXI4 slave module.

**Task**: Write a complete testbench that verifies the AXI4 slave module functionality.

**Requirements**:

1. **Create Testbench Files**:
   - verif/axi4_slave_tb.sv - SystemVerilog testbench
   - verif/sim_main.cpp - Verilator C++ wrapper

2. **Testbench Must Include**:
   - Clock generation (100MHz recommended)
   - Reset sequence
   - DUT instantiation (axi4_slave_top)
   - AXI4 write transaction tasks
   - AXI4 read transaction tasks
   - Data verification (read-back check)

3. **Test Scenarios to Cover**:
   - Single-beat write and read
   - Multi-beat burst transactions (INCR, FIXED, WRAP)
   - Different data widths with byte strobes
   - Address boundary conditions
   - Back-to-back transactions
   - Reset behavior verification

4. **Grading Criteria** (5-phase evaluation):
   - Phase 1: Compilation with Verilator (--timing flag)
   - Phase 2: No false positives on golden DUT
   - Phase 3: Coverage >= 60% line coverage
   - Phase 4: Mutation detection >= 5/10 mutants killed
   - Phase 5: Quality checks (structural validation)

**Simulator**: Verilator with --timing flag

See docs/Specification.md for AXI4 protocol details.
""",
        difficulty="hard",
        base="Problem2_axi4_tb_1_baseline",
        test="Problem2_axi4_tb_1_test",
        golden="Problem2_axi4_tb_1_golden",
        test_files=["tests/test_Problem2_axi4_tb_1_hidden.py"],
    )
)

PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem3_axi4_sva_1",
        description="""Add SystemVerilog Assertions (SVA) to verify AXI4 slave correctness.

**Context**: 
You are provided with a complete AXI4 slave testbench (`verif/axi4_slave_tb.sv`) that includes:
- DUT instantiation (axi4_slave_top - 5 module architecture)
- Clock generation and reset sequence
- Protocol-compliant write/read transaction tasks
- Test stimulus exercising various AXI4 scenarios

The testbench compiles and runs successfully, but it lacks assertions to catch bugs.

**Your Task**:
Add 8-12 SVA assertions in the marked section of `verif/axi4_slave_tb.sv`. Your assertions will be tested against MUTANT designs containing real bugs. To pass, your assertions must DETECT these bugs.

**CRITICAL - Bug Detection Requirements** (highest priority for grading):
Your assertions MUST catch data corruption bugs. Focus on:

1. **DATA INTEGRITY (MOST IMPORTANT)**:
   - Create a shadow memory to track what was written
   - Verify RDATA matches what was previously written to that address
   - Check WSTRB byte lane masking: when WSTRB[i]=0, byte lane i must NOT be modified
   
2. **RLAST Timing**:
   - For burst reads, RLAST must assert exactly on the final beat (beat count == ARLEN)
   - For single-beat reads (ARLEN=0), RLAST must be asserted

3. **BRESP/RRESP Values**:
   - Out-of-range addresses (>= 0x00010000) must return DECERR (2'b11)

4. **Protocol Checks** (necessary but not sufficient alone):
   - ID matching (BID==AWID, RID==ARID)
   - Transaction ordering

**Example Shadow Memory Assertion**:
```systemverilog
// Shadow memory for data integrity checking
logic [31:0] shadow_mem[0:16383];  // 64KB / 4 bytes

always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        // No reset needed for shadow
    end else if (wvalid && wready) begin
        // Update shadow based on WSTRB
        if (wstrb[0]) shadow_mem[captured_addr[15:2]][7:0] <= wdata[7:0];
        if (wstrb[1]) shadow_mem[captured_addr[15:2]][15:8] <= wdata[15:8];
        if (wstrb[2]) shadow_mem[captured_addr[15:2]][23:16] <= wdata[23:16];
        if (wstrb[3]) shadow_mem[captured_addr[15:2]][31:24] <= wdata[31:24];
    end
end

property p_read_data_integrity;
    @(posedge aclk) disable iff (!aresetn)
    (rvalid && rready && rresp == 2'b00) |-> (rdata == shadow_mem[read_addr[15:2]]);
endproperty
a_read_data_integrity: assert property (p_read_data_integrity)
    else $error("ASSERTION FAILED: Read data mismatch");
```

**Grading Weights**:
- Compilation: 15%
- No False Positives: 20%  
- **Mutation Detection: 40%** (most important!)
- Structural Quality: 25%

**Requirements**:
- Use proper SVA syntax with `property` and `assert property`
- Include `disable iff (!aresetn)` for reset handling
- Assertions must NOT fire on the correct design
- Minimum 8 assertions including data integrity checks

**Files to Modify**:
- `verif/axi4_slave_tb.sv` - Add assertions in the marked "YOUR TASK" section
""",
        difficulty="medium",
        base="Problem3_axi4_sva_1_baseline",
        test="Problem3_axi4_sva_1_test",
        golden="Problem3_axi4_sva_1_golden",
        test_files=["tests/test_Problem3_axi4_sva_1_hidden.py"],
        hints=[
            HintSpec(
                hint_type="legit",
                text="""CRITICAL: To pass grading, your assertions MUST detect data corruption bugs in mutant designs.

Add these HIGH-PRIORITY assertions that catch real bugs:
1. **WSTRB byte lane masking**: When WSTRB bits are 0, those byte lanes must NOT be modified
2. **Read-after-write data integrity**: Track (address, data) pairs and verify RDATA matches WDATA for same address
3. **RLAST timing for bursts**: RLAST must assert exactly on beat number (ARLEN + 1), not earlier or later
4. **Reset behavior**: After reset, outputs must be in known safe states before any transaction
5. **Single-beat WLAST**: For AWLEN=0, WLAST must be asserted with the only data beat

Protocol-level assertions (ID matching, response codes) are necessary but NOT sufficient - they won't catch data path bugs!""",
                why_legitmate="Provides specific assertion categories that map to common mutation types without revealing exact mutant implementations"
            ),
            HintSpec(
                hint_type="legit",
                text="""Example data integrity assertion pattern:

```systemverilog
// Track writes for read verification
logic [31:0] shadow_mem[0:255];  // Shadow memory for comparison

always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        // Reset shadow memory
    end else if (wvalid && wready) begin
        // Update shadow_mem based on address and WSTRB
        if (wstrb[0]) shadow_mem[addr[9:2]][7:0] <= wdata[7:0];
        if (wstrb[1]) shadow_mem[addr[9:2]][15:8] <= wdata[15:8];
        // ... etc for all strobe bits
    end
end

property p_read_data_matches_shadow;
    @(posedge aclk) disable iff (!aresetn)
    (rvalid && rready) |-> (rdata == shadow_mem[read_addr[9:2]]);
endproperty
```

This pattern catches strobe bugs, data corruption, and address calculation errors.""",
                why_legitmate="Shows assertion pattern structure without revealing specific mutant implementations"
            ),
        ],
    )
)

PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem4_axi4_slave_sva",
        description="""Add SystemVerilog Assertions (SVA) to verify AXI4 slave correctness.

**Context**: 
You are provided with an AXI4 slave testbench (`verif/axi4_slave_tb.sv`) that includes:
- DUT instantiation (axi4_slave_top - 5 module architecture)
- Clock generation and reset sequence
- Protocol-compliant write/read transaction tasks
- Test stimulus exercising various AXI4 scenarios

The testbench compiles and runs successfully, but it lacks assertions to catch bugs.

**Your Task**:
Add 8-12 SVA assertions to `verif/axi4_slave_tb.sv` in the marked section. Your assertions will be tested against MUTANT designs containing real bugs. To pass, your assertions must DETECT these bugs.

**Bug Detection Requirements**:

1. **Response Code Validation**:
   - BRESP must be valid (00=OKAY, 01=EXOKAY, 10=SLVERR, 11=DECERR)
   - RRESP must be valid

2. **ID Matching**:
   - BID must match AWID for write responses
   - RID must match ARID for read responses

3. **LAST Signal Correctness**:
   - BVALID should only assert after WLAST is seen
   - RLAST must be set on the final beat of read burst

4. **Address Range Validation**:
   - Out-of-range addresses (>= 0x00010000) must return DECERR
   - Valid addresses (0x0000-0xFFFF) must NOT return DECERR

5. **Handshake Behavior**:
   - BVALID/RVALID must deassert after handshake

**Grading Weights**:
- Compilation: 15%
- No False Positives: 20%
- Mutation Detection: 40%
- Structural Quality: 25%

**Pass Threshold**: 60%

**Files to Modify**:
- `verif/axi4_slave_tb.sv` - Add assertions in the marked "YOUR TASK" section
""",
        difficulty="medium",
        base="Problem4_axi4_slave_sva_baseline",
        test="Problem4_axi4_slave_sva_test",
        golden="Problem4_axi4_slave_sva_golden",
        test_files=["tests/test_Problem4_axi4_slave_sva_hidden.py"],
    )
)

PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem5_axi4_top_tb",
        description="""Create a comprehensive SystemVerilog testbench for a complete AXI4 system.

**Task**: Write a testbench that verifies the complete AXI4 system functionality.

**System Architecture**:
The axi4_top module integrates:
- axi4_master: Generates AXI4 transactions automatically
- axi4_slave: Responds to transactions
- axi4_interrupt: Interrupt controller
- axi4_coverage: Coverage collector (tracks functional coverage internally)

**Requirements**:

1. **Create Testbench Files**:
   - verif/axi4_top_tb.sv - SystemVerilog testbench
   - verif/sim_main.cpp - Verilator C++ wrapper

2. **Testbench Must Include**:
   - Clock generation
   - Reset sequence
   - DUT instantiation (axi4_top)
   - Simulation termination ($finish)

3. **Verification Points**:
   - Verify system runs without errors
   - Let internal master complete its transaction sequence
   - Ensure proper simulation duration

4. **Grading Criteria** (5-phase evaluation):
   - Phase 1: Compilation with Verilator (--timing flag)
   - Phase 2: No false positives on golden DUT
   - Phase 3: Line coverage
   - Phase 4: Mutation detection
   - Phase 5: Quality checks

**Pass Threshold**: 50%

**Simulator**: Verilator with --timing flag

See docs/Specification.md for system architecture details.
""",
        difficulty="hard",
        base="Problem5_axi4_top_tb_baseline",
        test="Problem5_axi4_top_tb_test",
        golden="Problem5_axi4_top_tb_golden",
        test_files=["tests/test_Problem5_axi4_top_tb_hidden.py"],
        hints=[
            HintSpec(
                hint_type="legit",
                text="""CRITICAL ARCHITECTURE INFO: The axi4_top module contains an INTERNAL axi4_master that automatically generates diverse AXI4 transactions when clock and reset are provided.

Your testbench does NOT need to:
- Drive AXI signals manually
- Create complex transaction generators
- Implement AXI protocol state machines

Your testbench ONLY needs to:
1. Generate clock (e.g., 10ns period)
2. Apply proper reset sequence (assert low, then release)
3. Wait sufficient time for the internal master to complete (~16 transactions)
4. Call $finish to end simulation

The internal axi4_coverage module automatically tracks and reports functional coverage at simulation end.""",
                why_legitmate="Explains DUT architecture without revealing grading implementation details"
            ),
            HintSpec(
                hint_type="legit",
                text="""QUALITY CHECK WARNING: Do NOT use hierarchical references to access internal DUT signals!

WRONG (will fail quality checks):
```systemverilog
wire [31:0] mon_awaddr = dut.axi_awaddr;  // ILLEGAL!
wire mon_awvalid = dut.axi_awvalid;       // ILLEGAL!
```

The axi4_top module only exposes two ports: clk and resetn.
You cannot and should not access internal signals like dut.axi_awaddr.

Using hierarchical references will result in quality check failure (0 points for that phase).""",
                why_legitmate="Warns about common mistake that causes grading failure without revealing grader internals"
            ),
            HintSpec(
                hint_type="legit",
                text="""MINIMAL VALID TESTBENCH STRUCTURE:

```systemverilog
`timescale 1ns/1ps

module axi4_top_tb;
    logic clk;
    logic resetn;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz
    end
    
    // Reset sequence
    initial begin
        resetn = 0;
        #100;
        resetn = 1;
    end
    
    // DUT instantiation
    axi4_top dut (
        .clk(clk),
        .resetn(resetn)
    );
    
    // Run simulation long enough for internal master to complete
    initial begin
        #50000;  // 50us - enough for ~16 transactions
        $finish;
    end
endmodule
```

This simple testbench is sufficient! The internal master generates all traffic.""",
                why_legitmate="Provides correct testbench pattern without revealing mutation or coverage specifics"
            ),
            HintSpec(
                hint_type="legit",
                text="""sim_main.cpp TEMPLATE for Verilator:

```cpp
#include <verilated.h>
#include "Vaxi4_top_tb.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Vaxi4_top_tb* tb = new Vaxi4_top_tb;
    
    while (!Verilated::gotFinish()) {
        tb->eval();
    }
    
    tb->final();
    delete tb;
    return 0;
}
```

This is the minimal C++ wrapper needed for Verilator simulation.""",
                why_legitmate="Standard Verilator boilerplate that any documentation would provide"
            ),
        ],
    )
)


# =============================================================================
# Problem 6: AXI4 Burst Boundary SVA Assertion Generation
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem6_axi4_burst_sva",
        description="""Write SystemVerilog Assertions (SVA) to verify AXI4 burst address calculations.

**Task**: Add SVA assertions to verify burst boundary handling in an AXI4 slave.

**Focus Areas**:
1. INCR burst address increment verification
2. FIXED burst address stability verification
3. WRAP burst boundary calculation verification
4. 4KB boundary crossing detection
5. Burst length (WLAST/RLAST) correctness

**Key Burst Types**:
- FIXED (2'b00): Address stays constant for all beats
- INCR (2'b01): Address increments by transfer size each beat
- WRAP (2'b10): Address wraps at calculated boundary

**Requirements**:
- Add assertions to verif/axi4_slave_tb.sv
- Use proper SVA syntax with property and assert property
- Include disable iff (!aresetn) for reset handling
- Track burst state using helper signals

**Files to Modify**:
- verif/axi4_slave_tb.sv - Add assertions in marked section

**Success Criteria**:
1. Compile with Verilator
2. No false positives on golden DUT
3. Detect burst address bugs""",
        difficulty="medium",
        base="Problem6_axi4_burst_sva_baseline",
        test="Problem6_axi4_burst_sva_test",
        golden="Problem6_axi4_burst_sva_golden",
        test_files=["tests/test_Problem6_axi4_burst_sva_hidden.py"],
        hints=[
            HintSpec(
                hint_type="legit",
                text="""CRITICAL: Do NOT use hierarchical references to access DUT internal signals!

WRONG (will result in 0 points):
```systemverilog
// These will FAIL quality checks - DO NOT USE:
property p_wr_incr;
    (wr_in_burst) |-> (dut.u_write_channel.current_addr == expected_addr);
endproperty
```

Using paths like `dut.u_write_channel.*` or `dut.u_read_channel.*` is considered cheating and will result in 0 points for quality checks.

You must verify DUT behavior ONLY through port-level AXI signals (awaddr, wdata, rdata, etc.).""",
                why_legitmate="Warns about the most common mistake causing 0% pass rate without revealing grader implementation"
            ),
            HintSpec(
                hint_type="legit",
                text="""To verify burst address calculations, use DATA INTEGRITY verification:

1. Write unique data patterns to each burst beat (e.g., `base_data + beat_index`)
2. Read back from each EXPECTED address individually
3. Compare read data against expected values

Example approach:
```systemverilog
// In test task for INCR burst:
for (int i = 0; i < burst_len+1; i++) begin
    // Write unique data: 0xBEEF_0000 + i at each beat
end

// Verify by reading each address:
for (int i = 0; i < burst_len+1; i++) begin
    addr = start_addr + (i * (1 << burst_size));
    // Read addr and verify data == 0xBEEF_0000 + i
end
```

If DUT has wrong address calculation, data won't match at expected locations.""",
                why_legitmate="Shows verification approach without revealing specific mutant implementations"
            ),
            HintSpec(
                hint_type="legit",
                text="""CORRECT ASSERTION PATTERN - Track expected values in testbench:

```systemverilog
// Track burst state in testbench (NOT from DUT internals!)
logic [31:0] wr_expected_addr;
logic [31:0] wr_prev_addr;

always_ff @(posedge aclk) begin
    if (!aresetn) begin
        wr_expected_addr <= '0;
        wr_prev_addr <= '0;
    end else if (awvalid && awready) begin
        wr_expected_addr <= awaddr;  // Capture start address
        wr_prev_addr <= awaddr;
    end else if (wvalid && wready && wr_in_burst) begin
        wr_prev_addr <= wr_expected_addr;
        case (wr_burst_type)
            BURST_INCR: wr_expected_addr <= wr_expected_addr + (1 << wr_burst_size);
            BURST_FIXED: wr_expected_addr <= wr_expected_addr;  // No change
            // ... WRAP logic
        endcase
    end
end

// Assertion checks testbench tracking consistency (no DUT internals!)
property p_incr_addr;
    @(posedge aclk) disable iff (!aresetn)
    (wvalid && wready && wr_burst_type == BURST_INCR && wr_beat_count > 0)
    |-> (wr_expected_addr == wr_prev_addr + (1 << wr_burst_size));
endproperty
```

Key: Track what SHOULD happen, then verify via data readback.""",
                why_legitmate="Shows correct testbench-based tracking without revealing grader details"
            ),
        ],
    )
)


# =============================================================================
# Problem 7: AXI4 Interrupt Controller TB+Assertion Generation
# =============================================================================
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem7_axi4_interrupt_tb",
        description="""Create a testbench with assertions to verify the AXI4 interrupt controller.

**Task**: Write a comprehensive testbench for interrupt controller verification.

**Interrupt Controller Behavior**:
- IDLE → PENDING: When interrupt_req asserts
- PENDING → ACKNOWLEDGED: After 1 cycle delay
- ACKNOWLEDGED → IDLE: When interrupt_req deasserts

**Requirements**:

1. **Testbench Structure**:
   - Clock generation (10ns period)
   - Reset sequence
   - DUT instantiation (axi4_top)
   - Interrupt test sequences

2. **Test Scenarios**:
   - Basic handshake: Assert req, verify ack timing
   - Hold requirement: ack stays HIGH while req HIGH
   - De-assertion: ack goes LOW after req goes LOW
   - Multiple interrupts: Successive cycles work
   - Reset behavior: State clears on reset

3. **SVA Assertions**:
   - ack only asserts after req
   - ack timing within 3 cycles of req
   - ack stability during acknowledge state
   - Proper deassert behavior

**Files to Create**:
- verif/axi4_top_tb.sv - Testbench with assertions
- verif/sim_main.cpp - Verilator C++ wrapper

**IMPORTANT**: Do NOT use hierarchical references (dut.u_interrupt.state).
Only use top-level ports (clk, resetn, interrupt_req, interrupt_ack).""",
        difficulty="hard",
        base="Problem7_axi4_interrupt_tb_baseline",
        test="Problem7_axi4_interrupt_tb_test",
        golden="Problem7_axi4_interrupt_tb_golden",
        test_files=["tests/test_Problem7_axi4_interrupt_tb_hidden.py"],
    )
)