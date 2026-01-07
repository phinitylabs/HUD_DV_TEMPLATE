# Design Verification (DV) Agent Evaluation Framework

## Overview

This framework is designed for creating and evaluating **Design Verification** tasks for AI agents. It focuses on:
- SystemVerilog testbench creation
- SVA (SystemVerilog Assertions) generation
- Mutation testing for assertion quality validation
- Coverage-based grading

## Project Structure

```
.
├── src/hud_controller/          # Main framework code
│   ├── app.py                   # Main MCP server and entry points
│   ├── spec.py                  # Core specifications (Problem, Grade, Grader)
│   ├── grading_runner.py        # Test execution and grading logic
│   ├── problems/                # Task definitions
│   │   └── basic.py             # Problem definitions with hints
│   └── tools/                   # MCP tools for testing
├── utils/
│   └── imagectl3.py             # Docker image build/validate/push utility
├── pyproject.toml               # Python package configuration
├── Dockerfile                   # Container setup with Verilator
└── README.md                    # This file
```

## DV Problem Examples

### Example 1: SVA Assertion Generation (Problem 3)

This is a mutation-testing based problem where the agent must write assertions that catch bugs:

```python
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem3_axi4_sva_1",
        description="""Add SystemVerilog Assertions (SVA) to verify AXI4 slave correctness.

**Context**: 
You are provided with a complete AXI4 slave testbench that includes:
- DUT instantiation (axi4_slave_top)
- Clock generation and reset sequence
- Protocol-compliant write/read transaction tasks

The testbench compiles and runs successfully, but lacks assertions to catch bugs.

**Your Task**:
Add 8-12 SVA assertions in the marked section of `verif/axi4_slave_tb.sv`. 
Your assertions will be tested against MUTANT designs containing real bugs.
To pass, your assertions must DETECT these bugs.

**Target Bug Categories**:
1. AXI4 handshake violations
2. Write strobe (WSTRB) handling errors  
3. Response code bugs
4. Burst counter errors
5. Reset behavior issues

**Grading Criteria**:
- Phase 1: Compilation (15%) - Must compile with Verilator
- Phase 2: No False Positives (20%) - No assertions fire on golden DUT
- Phase 3: Mutation Testing (40%) - Kill 3+ of 5 mutants
- Phase 4: Structural Quality (25%) - Proper SVA syntax, no cheating
""",
        difficulty="medium",
        base="Problem3_axi4_sva_1_baseline",
        test="Problem3_axi4_sva_1_test",
        golden="Problem3_axi4_sva_1_golden",
        test_files=["tests/test_Problem3_axi4_sva_1_hidden.py"],
        hints=[
            HintSpec(
                hint_type="legit",
                text="""Use proper SVA syntax with disable iff for reset:
```systemverilog
property p_awvalid_stable;
    @(posedge aclk) disable iff (!aresetn)
    (awvalid && !awready) |=> awvalid;
endproperty
assert property (p_awvalid_stable);
```""",
                why_legitmate="Shows SVA syntax without revealing specific bugs"
            ),
        ],
    )
)
```

### Example 2: Comprehensive Testbench Creation (Problem 2)

```python
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem2_axi4_tb_1",
        description="""Create a comprehensive SystemVerilog testbench for an AXI4 slave module.

**Task**: Write a complete testbench that verifies the AXI4 slave functionality.

**Requirements**:

1. **Create Testbench Files**:
   - verif/axi4_slave_tb.sv - SystemVerilog testbench
   - verif/sim_main.cpp - Verilator C++ wrapper

2. **Testbench Must Include**:
   - Clock generation (100MHz recommended)
   - Reset sequence
   - DUT instantiation
   - AXI4 write transaction tasks
   - AXI4 read transaction tasks
   - Data verification (read-back check)

3. **Test Scenarios to Cover**:
   - Single-beat write and read
   - Multi-beat burst transactions (INCR, FIXED, WRAP)
   - Different data widths with byte strobes
   - Address boundary conditions

**Grading Criteria** (5-phase evaluation):
- Phase 1: Compilation with Verilator
- Phase 2: No false positives on golden DUT
- Phase 3: Coverage >= 60% line coverage
- Phase 4: Mutation detection >= 5/10 mutants killed
- Phase 5: Quality checks (structural validation)
""",
        difficulty="hard",
        base="Problem2_axi4_tb_1_baseline",
        test="Problem2_axi4_tb_1_test",
        golden="Problem2_axi4_tb_1_golden",
        test_files=["tests/test_Problem2_axi4_tb_1_hidden.py"],
    )
)
```

## Creating New DV Tasks

### What You Need to Create

For each DV problem, you need to prepare:

| Component | Description | Location |
|-----------|-------------|----------|
| **Baseline Branch** | Starting code with DUT, partial/empty testbench | `{problem_id}_baseline` branch in target repo |
| **Test Branch** | Hidden grader + mutants (extends baseline) | `{problem_id}_test` branch |
| **Golden Branch** | Reference solution (extends baseline) | `{problem_id}_golden` branch |
| **Problem Spec** | Task description, hints | `src/hud_controller/problems/basic.py` |
| **Hidden Grader** | Python test file with grading logic | `tests/test_{problem_id}_hidden.py` |
| **Mutants** (optional) | Buggy DUT variants for mutation testing | `tests/mutants/M01_*/`, `tests/mutants/M02_*/` |

### Step 1: Create Git Branches in Target Repository

**Baseline Branch** (`{problem_id}_baseline`):
```
├── sources/           # DUT RTL files
│   ├── axi4_slave.sv
│   └── axi4_pkg.sv
├── verif/             # Empty or partial testbench
│   └── axi4_slave_tb.sv   # Agent will modify this
├── docs/
│   └── Specification.md   # Protocol/design documentation
└── Makefile           # Build commands
```

**Test Branch** (`{problem_id}_test`):
```
├── tests/
│   ├── test_{problem_id}_hidden.py   # Hidden grader
│   ├── grader.py                      # Grading logic
│   └── mutants/                       # For mutation testing
│       ├── M01_bug_name/
│       │   └── axi4_slave.sv          # Buggy variant
│       ├── M02_another_bug/
│       │   └── axi4_slave.sv
│       └── ...
└── (all baseline files)
```

**Golden Branch** (`{problem_id}_golden`):
```
├── verif/
│   └── axi4_slave_tb.sv   # Complete reference solution
└── (all baseline files, NO test files)
```

### Step 2: Create the Hidden Grader

The grader runs multiple phases:

```python
# tests/test_{problem_id}_hidden.py
import pytest
from tests.grader import DVGrader

WEIGHTS = {
    "compilation": 0.15,      # Must compile with Verilator
    "no_false_positives": 0.20,  # No errors on golden DUT
    "mutation": 0.40,         # Mutants killed / total mutants
    "structural": 0.25,       # Code quality checks
}

PASS_THRESHOLD = 0.60  # 60% to pass

class TestDVGeneration:
    def test_dv_task(self):
        grader = DVGrader(
            tb_path="verif/axi4_slave_tb.sv",
            sources_dir="sources",
            mutants_dir="tests/mutants"
        )
        result = grader.grade()
        
        # Calculate weighted score
        total = (
            result.compiled * WEIGHTS["compilation"] +
            result.no_false_positives * WEIGHTS["no_false_positives"] +
            result.mutation_score * WEIGHTS["mutation"] +
            result.structural_score * WEIGHTS["structural"]
        )
        
        assert total >= PASS_THRESHOLD, f"Score {total:.1%} < {PASS_THRESHOLD:.0%}"
```

### Step 3: Create Mutants for Mutation Testing

Each mutant is a buggy version of the DUT that good assertions should catch:

```
tests/mutants/
├── M01_handshake_bug/
│   └── axi4_slave.sv     # Bug: AWREADY doesn't wait for AWVALID
├── M02_wstrb_ignored/
│   └── axi4_slave.sv     # Bug: Write strobe is ignored
├── M03_burst_counter/
│   └── axi4_slave.sv     # Bug: Burst counter wraps incorrectly
├── M04_reset_bug/
│   └── axi4_slave.sv     # Bug: State not cleared on reset
└── M05_response_code/
    └── axi4_slave.sv     # Bug: Wrong response code generated
```

### Step 4: Add Anti-Cheat Checks

Prevent agents from "cheating" by:

```python
# In grader.py - phase4_structural()
def check_quality(self, tb_content: str) -> StructuralResult:
    result = StructuralResult()
    
    # Check for hierarchical references (cheating!)
    if re.search(r'dut\.\w+_channel\.', tb_content):
        result.illegal_patterns.append("Hierarchical reference to DUT internals")
    
    # Check for hardcoded errors (not real assertions)
    if re.search(r'initial\s+begin.*\$error', tb_content, re.DOTALL):
        result.illegal_patterns.append("Hardcoded $error")
    
    # Verify minimum assertion count
    assertions = re.findall(r'assert\s+property', tb_content)
    result.assertion_count = len(assertions)
    
    return result
```

### Step 5: Add Problem Definition with Hints

```python
# src/hud_controller/problems/basic.py
PROBLEM_REGISTRY.append(
    ProblemSpec(
        id="Problem3_axi4_sva_1",
        description="""...""",  # Task description
        difficulty="medium",    # easy, medium, hard
        base="Problem3_axi4_sva_1_baseline",
        test="Problem3_axi4_sva_1_test", 
        golden="Problem3_axi4_sva_1_golden",
        test_files=["tests/test_Problem3_axi4_sva_1_hidden.py"],
        hints=[
            HintSpec(
                hint_type="legit",
                text="""Your hint text here...""",
                why_legitmate="Explains why this hint is fair"
            ),
        ],
    )
)
```

### Step 6: Validate Your Problem

```bash
# Build and validate the Docker image
uv run utils/imagectl3.py verilog --ids Problem3_axi4_sva_1 -b -v

# With hints enabled
uv run utils/imagectl3.py verilog --ids Problem3_axi4_sva_1 -b -v --hints all

# Parallel build/validate for multiple problems
uv run utils/imagectl3.py verilog -bv --jobs 4
```

Validation checks:
1. ✅ Baseline compiles
2. ✅ Test patch applies and fails tests (baseline has bugs)
3. ✅ Golden patch applies and passes tests

## Running Evaluations

### Local Evaluation
```bash
uv run hud eval local-hud.json claude --max-steps 50
```

### Remote Evaluation (requires Docker Hub push)
```bash
# Build, validate, and push
uv run utils/imagectl3.py dockerhub_username/verilog -bvp --jobs 4

# Run remote eval
uv run hud eval remote-hud.json claude --max-steps 50
```

## Grading Weights (Typical DV Problem)

| Phase | Weight | Description |
|-------|--------|-------------|
| Compilation | 15% | Code compiles with Verilator |
| No False Positives | 20% | No assertion fires on golden DUT |
| Mutation Testing | 40% | Percentage of mutants killed |
| Structural Quality | 25% | Proper syntax, no cheating |

**Pass Threshold**: Usually 60%

## Best Practices for DV Tasks

### Task Design
1. **Clear Bug Categories**: Define what types of bugs assertions should catch
2. **Realistic Mutants**: Create mutants based on real design bugs
3. **Fair Grading**: Balance mutation difficulty - not too easy, not impossible
4. **Helpful Hints**: Guide syntax without revealing specific bugs

### Mutant Design
1. **Single Bug Per Mutant**: Each mutant should have one focused bug
2. **Catchable Bugs**: Bugs should be detectable via external interface
3. **Documented Bugs**: Comment what's wrong in each mutant file
4. **Varied Categories**: Cover different bug types (timing, logic, protocol)

### Anti-Cheat
1. **Block Hierarchical References**: Agents shouldn't peek at DUT internals
2. **Require Real Assertions**: Not just `$error` in initial blocks
3. **Minimum Assertion Count**: Require enough assertions for coverage
