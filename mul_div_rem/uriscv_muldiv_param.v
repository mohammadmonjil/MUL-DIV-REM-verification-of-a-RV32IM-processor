//-----------------------------------------------------------------
//                          uRISC-V CPU
//                            V0.5.0
//               github.com/ultraembedded/core_uriscv
//                     Copyright 2015-2021
//
//                   admin@ultra-embedded.com
//
//                     License: Apache 2.0
//-----------------------------------------------------------------
// Copyright 2015-2021 github.com/ultraembedded
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//-----------------------------------------------------------------
module uriscv_muldiv_param
#(
    // Operand width
    localparam N = 16
)
(
    input               clk_i,
    input               rst_i,

    // Operation select
    input               valid_i,
    input               inst_mul_i,
    input               inst_mulh_i,
    input               inst_mulhsu_i,
    input               inst_mulhu_i,
    input               inst_div_i,
    input               inst_divu_i,
    input               inst_rem_i,
    input               inst_remu_i,

    // Operands
    input  [N-1:0]      operand_ra_i,
    input  [N-1:0]      operand_rb_i,

    // Result
    output              stall_o,
    output              ready_o,
    output [N-1:0]      result_o
);


//-----------------------------------------------------------------
// Includes
//-----------------------------------------------------------------
// `include "uriscv_defs.v"

//-------------------------------------------------------------
// Multiplier
//-------------------------------------------------------------
reg [N:0]   mul_operand_a_q;
reg [N:0]   mul_operand_b_q;
reg          mulhi_sel_q;

//-------------------------------------------------------------
// Multiplier
//-------------------------------------------------------------
wire [N*2:0]  mult_result_w;
reg  [N:0]  operand_b_r;
reg  [N:0]  operand_a_r;
reg  [N-1:0]  mul_result_r;

wire mult_inst_w    = inst_mul_i     |
                      inst_mulh_i    |
                      inst_mulhsu_i  |
                      inst_mulhu_i;


always @ *
begin
    if (inst_mulhsu_i)
        operand_a_r = {operand_ra_i[N-1], operand_ra_i[N-1:0]};
    else if (inst_mulh_i)
        operand_a_r = {operand_ra_i[N-1], operand_ra_i[N-1:0]};
    else // MULHU || MUL
        operand_a_r = {1'b0, operand_ra_i[N-1:0]};
end

always @ *
begin
    if (inst_mulhsu_i)
        operand_b_r = {1'b0, operand_rb_i[N-1:0]};
    else if (inst_mulh_i)
        operand_b_r = {operand_rb_i[N-1], operand_rb_i[N-1:0]};
    else // MULHU || MUL
        operand_b_r = {1'b0, operand_rb_i[N-1:0]};
end

// Pipeline flops for multiplier
always @(posedge clk_i )
if (rst_i)
begin
    mul_operand_a_q <= {N+1{1'b0}};
    mul_operand_b_q <= {N+1{1'b0}};
    mulhi_sel_q     <= 1'b0;
end
else if (valid_i && mult_inst_w)
begin
    mul_operand_a_q <= operand_a_r;
    mul_operand_b_q <= operand_b_r;
    mulhi_sel_q     <= ~inst_mul_i;
end
else
begin
    mul_operand_a_q <= {N+1{1'b0}};
    mul_operand_b_q <= {N+1{1'b0}};
    mulhi_sel_q     <= 1'b0;
end

assign mult_result_w = {{ N {mul_operand_a_q[N]}}, mul_operand_a_q}*{{ N {mul_operand_b_q[N]}}, mul_operand_b_q};

always @ *
begin
    mul_result_r = mulhi_sel_q ? mult_result_w[N*2 -1:N] : mult_result_w[N-1:0];
end

reg mul_busy_q;

always @(posedge clk_i )
if (rst_i)
    mul_busy_q <= 1'b0;
else
    mul_busy_q <= valid_i & mult_inst_w;

//-------------------------------------------------------------
// Divider
//-------------------------------------------------------------
wire div_rem_inst_w     = inst_div_i  || 
                          inst_divu_i ||
                          inst_rem_i  ||
                          inst_remu_i;

wire signed_operation_w = inst_div_i || inst_rem_i;
wire div_operation_w    = inst_div_i || inst_divu_i;

reg [N-1:0] dividend_q;
reg [2*(N-1):0] divisor_q;
reg [N-1:0] quotient_q;
reg [N-1:0] q_mask_q;
reg        div_inst_q;
reg        div_busy_q;
reg        invert_res_q;

wire div_start_w    = valid_i & div_rem_inst_w & !stall_o;
wire div_complete_w = !(|q_mask_q) & div_busy_q;

always @ (posedge clk_i )
if (rst_i)
begin
    div_busy_q     <= 1'b0;
    dividend_q     <= {N{1'b0}};;
    divisor_q      <= { (2*N-1){1'b0}};
    invert_res_q   <= 1'b0;
    quotient_q     <= {N{1'b0}};;
    q_mask_q       <= {N{1'b0}};
    div_inst_q     <= 1'b0;
end 
else if (div_start_w)
begin
    div_busy_q     <= 1'b1;
    div_inst_q     <= div_operation_w;

    if (signed_operation_w && operand_ra_i[N-1])
        dividend_q <= -operand_ra_i;
    else
        dividend_q <= operand_ra_i;

    if (signed_operation_w && operand_rb_i[N-1])
        divisor_q <= {-operand_rb_i, {(N -1){1'b0}} };
    else
        divisor_q <= {operand_rb_i, {(N -1){1'b0}}};

    invert_res_q  <= (inst_div_i && (operand_ra_i[N-1] != operand_rb_i[N-1]) && |operand_rb_i) || 
                     (inst_rem_i && operand_ra_i[N-1]);

    quotient_q     <= {N {1'b0}} ;
    q_mask_q       <= {1'b1, {(N-1){1'b0}}} ;
end
else if (div_complete_w)
begin
    div_busy_q <= 1'b0;
end
else if (div_busy_q)
begin
    if (divisor_q <= {{N-1{1'b0}} , dividend_q})
    begin
        dividend_q <= dividend_q - divisor_q[N-1:0];
        quotient_q <= quotient_q | q_mask_q;
    end

    divisor_q <= {1'b0, divisor_q[2*(N-1):1]};
    q_mask_q  <= {1'b0, q_mask_q[N-1:1]};
end

reg [N-1:0] div_result_r;
always @ *
begin
    div_result_r = {N{1'b0}};;

    if (div_inst_q)
        div_result_r = invert_res_q ? -quotient_q : quotient_q;
    else
        div_result_r = invert_res_q ? -dividend_q : dividend_q;
end

//-------------------------------------------------------------
// Shared logic
//-------------------------------------------------------------

// Stall if divider logic is busy and new multiplier or divider op
assign stall_o = (div_busy_q  & (mult_inst_w | div_rem_inst_w)) ||
                 (mul_busy_q & div_rem_inst_w);

reg  [N-1:0]  result_q;
reg          ready_q;

always @ (posedge clk_i )
if (rst_i)
    ready_q <= 1'b0;
else if (mul_busy_q)
    ready_q <= 1'b1;
else if (div_complete_w)
    ready_q <= 1'b1;
else
    ready_q <= 1'b0;

always @ (posedge clk_i )
if (rst_i)
    result_q <= {N{1'b0}};
else if (div_complete_w)
    result_q <= div_result_r;
else if (mul_busy_q)
    result_q <= mul_result_r;

assign result_o  = result_q;
assign ready_o   = ready_q;

endmodule
