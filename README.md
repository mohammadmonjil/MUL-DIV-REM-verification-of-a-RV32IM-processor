# MUL-DIV-REM-verification-of-a-RV32IM-processor
This project focuses on the **formal verification of MUL, DIV, and REM instructions** in a **sequential RV32IM RISC-V processor**, based on the [`core_uriscv`](https://github.com/ultraembedded/core_uriscv) design from UltraEmbedded.

## Overview

I recently took on the challenge of verifying the multiplier, divisor, and remainder instructions of an open source RV32IM processor using Cadence JasperGold. 
My initial goal was to prove:  

```
After instruction retirement,
the destination register holds the correct results of mul/div/rem operations on the source registers.
```

However, directly verifying 32-bit multiplication/division instructions ran into state explosion, making proofs infeasible. 

To address this, I attempted block-level verification of the multiplier/divisor unit. Even then, 32-bit operands were too large, so I parameterized the design to reduce operand width to 16 bits. This allowed the block to be formally verified within a reasonable time. 

Next, I blackboxed the multiplier and applied assumptions that tied outputs to correct values based on inputs. But state explosion persisted even with blackboxing! Because Jasper had to explore all input combinations anyway to satisfy the assumptions. 

Realizing that full end-to-end verification wasn’t tractable, I reframed the problem and proved two key properties instead: 

```
i) Correct source register values reach the inputs of the multiplier. 
ii) The multiplier’s output is written back to the correct destination register. 
```

Since the multiplier/divisor block itself is already verified (though at reduced width), these two properties together provide confidence that mul/div/rem instructions are correctly implemented at the processor level. 


1. **Multiplier/divisor block verification**:

The multiplier/divisor block `uriscv_muldiv.v` was not parameterized, the operands were all 32 bits which could not be verified directly. So I modified the block and create a parameterized version `uriscv_muldiv_param.v`. The localparam N can be used to change the operand length. I verified this block with N = 16. 

- File: `mul_div_test.sv`
- run `mul_div_block.tcl` in jasper.
- Verified all corner cases and state transitions for:
  - `MUL`, `MULH`, `MULHU`, `MULHSU`
  - `DIV`, `DIVU`, `REM`, `REMU`
- Focused on checking correctness of results based on standard RISC-V behavior.

2. **Blackboxing & MUL/DIV/REM instruction verification**:  
   Once verified, the block was blackboxed, and **assumptions** were written on its output control signals based on input control signals. We do not put any assumptions on the data output of the block, formal tool is free to put any value there. We only verify, that the multiplier/divisor block gets correct operands or register values (according to the opcode) in its input and the output of the block is written to the correct destination register according to instruction opcode.

We put assumptions on the output control signals of the multiplier block only. For example, after `valid_i` is asserted it will take 2 cycles for the output to appear for multiplication and 32 cycles for division/rem operations and the `ready_o` signal will be asserted.
- File: `multiplier_assumptions.sv`

As we blackboxed the multiplier, it is not possible to check the register value to see if we get the expected result (i.e. rd = rs1*rs2). But we can prove two properties that combined with verification on the multiplier we did previously can prove that the instruction exectutes correctly.

- First we can prove that the correct operands or the correct register values as denoted by the instruction reaches the inputs of the multiplier block.
  ```
      property source_reg_values_reach_mul_div_inputs;
        logic [31:0] rs1_val, rs2_val;

        @(posedge clk) disable iff (rst)
            (pc_inst_start && is_muldivrem(pc_instr),
                rs1_val = pc_reg[get_rs1(pc_instr)], rs2_val = pc_reg[get_rs2(pc_instr)])
            |-> mul_div_valid_i && (mul_div_operand_ra_i== rs1_val) && (mul_div_operand_rb_i == rs2_val) ;
    endproperty
  ```
- Second we can prove that the output of the multiplier when `ready_o` is asserted eventually reaches to the correct destination register according to the instruction opcode.
```
property result_of_mul_div_gets_written_to_destination_reg;
        logic [5:0] rd_addr;
        logic [31:0] mul_div_result;

        @(posedge clk) disable iff (rst)
            (pc_inst_start && is_muldivrem(pc_instr), rd_addr = get_rd(pc_instr))
            ##1 !mul_div_ready_o[*1:$]##1 (mul_div_ready_o, mul_div_result = mul_div_result_o) 
            ##1 !pc_inst_start[*1:$]##1 pc_inst_start
            |-> ( (rd_addr == 5'd0) ? (pc_reg[rd_addr] == 32'd0) : pc_reg[rd_addr] == mul_div_result) ;
    endproperty
```

These properties, along with the guarantee that the multipler/divisor block will produce the right output (We verified this guarantee in the block level verification) together proves correctness of MUL/DIV/REM instructions.

- File: `formal_tb.sv`

## How to Run

1. Run mul_div_instr.tcl

## Results

-  Correctness of all RISC-V M-extension instructions formally proven.

   
