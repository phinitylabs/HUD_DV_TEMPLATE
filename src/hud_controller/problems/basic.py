import logging

from hud_controller.spec import ProblemSpec, PROBLEM_REGISTRY

logger = logging.getLogger(__name__)


PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="simple_counter",
        description="""Please implement a simple synchronous counter that with reset, enable, and load functionality.
Inputs:
clk - Clock signal (triggers on rising edge)
rst - Synchronous reset signal
ena - Enable signal (allows counting)
set - Load signal (sets counter to a specific value)
din - 8-bit data input (value to load when set is high)
Output:
counter - 8-bit counter value        
        
""",
        difficulty="easy",
        base="simple_counter_baseline",
        test="simple_counter_test",
        golden="simple_counter_golden",
        test_files=["tests/test_simple_counter_hidden.py"],
    )
)

PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="simple_dff",
        description="""Please implement a simple digital flip-flop with a clock input and a data input. 
The output should be the same as the data input on the rising edge of the clock.

Inputs:
clk - Clock signal (triggers on rising edge)
d - Data input
Output:
q - Output value      
""",
        difficulty="easy",
        base="simple_dff_baseline",
        test="simple_dff_test",
        golden="simple_dff_golden",
        test_files=["tests/test_simple_dff_hidden.py"],
    )
)

PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="axi4_slave_sva",
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
        base="axi4_slave_sva_baseline",
        test="axi4_slave_sva_test",
        golden="axi4_slave_sva_golden",
        test_files=["tests/test_axi4_slave_sva_hidden.py"],
    )
)