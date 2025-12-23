import logging

from hud_controller.spec import ProblemSpec, PROBLEM_REGISTRY

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
        description="""Add SystemVerilog Assertions (SVA) to verify AXI4 protocol compliance.

**Context**: 
You are provided with a complete AXI4 slave testbench (`verif/axi4_slave_tb.sv`) that includes:
- DUT instantiation (axi4_slave_top - 5 module architecture)
- Clock generation and reset sequence
- Protocol-compliant write/read transaction tasks
- Test stimulus exercising various AXI4 scenarios

The testbench compiles and runs successfully, but it lacks protocol assertions.

**Your Task**:
Add 5-10 SVA assertions in the marked section of `verif/axi4_slave_tb.sv` to verify:
You are required to implement 5–10 SystemVerilog Assertions (SVA) in the marked section of `verif/axi4_slave_tb.sv` to explicitly verify the following AXI4 protocol properties:

1. **Response Validity**:
   - When BVALID is asserted, the BRESP value must be a legal AXI4 response code: only the 2-bit codes 2'b00 (OKAY), 2'b01 (EXOKAY), 2'b10 (SLVERR), or 2'b11 (DECERR) are allowed. Any other value is an error.
   - Similarly, RRESP must only take these legal response codes when RVALID is high.

2. **ID Matching**:
   - Whenever a write response is given (BVALID), the BID returned by the slave must exactly match the AWID that was provided on the corresponding write address channel for that transaction.
   - On each read response (RVALID), the RID value must match the ARID associated with the corresponding read transaction.

3. **Transaction Ordering**:
   - The AXI4 slave must never assert BVALID (write response valid) before it has received a write address (AWVALID/AWREADY handshake).
   - The slave must not assert RVALID (read response valid) before a read address has been accepted (ARVALID/ARREADY handshake).
   - Additionally, BVALID should not be asserted prior to the last data beat (WLAST) of a write transaction being received.

4. **DECERR Handling for Address Out-of-Range**:
   - If the slave is accessed with an address of 0x00010000 or greater, the returned response (BRESP or RRESP) must be DECERR (2'b11).

5. **LAST Signal Checks**:
   - For single-beat read transactions (where ARLEN is 0), the slave must assert RLAST with the read response.
   - For single-beat writes (AWLEN = 0), the testbench must provide WLAST with the only data beat.

For each property, write SVA assertions using the recommended pattern:
- Use `property`/`assert property`.
- Include `disable iff (!aresetn)` for asynchronous reset coverage.
- On assertion failure, issue `$error("ASSERTION FAILED: ...")` with a clear explanation.

It is your responsibility to craft these assertions using explicit logic to monitor relevant signals, track IDs across handshakes as needed, and ensure the protocol is followed under all test conditions. Avoid simply copying examples, but cover each of the listed requirements with robust assertions. Aim to write at least 8 total, grouped sensibly, and ensure they do NOT fire on the correct, specification-compliant design.

**Requirements**:
- Use proper SVA syntax with `property` and `assert property`
- Include `disable iff (!aresetn)` for reset handling
- Use `$error("ASSERTION FAILED: ...")` for failure messages
- Assertions must NOT fire on the correct (bug-free) design
- Minimum 5 assertions, recommended 8-10

**Example Assertion Format**:
```systemverilog
// Track state for assertion
logic some_flag;
always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn)
        some_flag <= 1'b0;
    else if (condition)
        some_flag <= 1'b1;
end

property p_example_check;
    @(posedge aclk) disable iff (!aresetn)
    trigger_signal |-> expected_condition;
endproperty

a_example_check: assert property (p_example_check)
    else $error("ASSERTION FAILED: description");
```

**Grading Criteria**:
1. **Compilation** - Testbench must compile without errors
2. **No False Positives** - Assertions must pass on the correct DUT
3. **Bug Detection** - Assertions must catch bugs in mutant designs
4. **Structural Quality** - Minimum 5 `assert property` statements

```

**Files to Modify**:
- `verif/axi4_slave_tb.sv` - Add assertions in the marked "YOUR TASK" section

**Reference**:
- See `docs/Specification.md` for AXI4 protocol details
- DUT sources in `sources/` directory
""",
        difficulty="medium",
        base="Problem3_axi4_sva_1_baseline",
        test="Problem3_axi4_sva_1_test",
        golden="Problem3_axi4_sva_1_golden",
        test_files=["tests/test_Problem3_axi4_sva_1_hidden.py"],
    )
)