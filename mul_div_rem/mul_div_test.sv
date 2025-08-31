// uriscv_muldiv_sva.sv
// Bind onto: module uriscv_muldiv

// ---------- Checker ----------
module mul_div_test (input logic clk_i, rst_i);
    localparam N = 16;
    localparam logic [N-1:0] INT_MIN = (1'b1 << (N-1));   // 100...0
    localparam logic [N-1:0] ALL1    = {N{1'b1}};         // 111...1

    function automatic [2*N -1 :0] mul_uu(input logic [N-1:0] a, b);
        mul_uu = $unsigned(a) * $unsigned(b);
    endfunction

    function automatic [2*N-1:0] mul_ss(input logic [N-1:0] a, b);
        mul_ss = $signed(a) * $signed(b);
    endfunction

    function automatic logic [2*N-1:0] mul_su(input logic [N-1:0] a, input logic [N-1:0] b);

        logic  [2*N-1:0] sa = ({{N{a[N-1]}}, a});         // sign-extend a
        logic  [2*N-1:0] ub = ({ {N{1'b0}} , b});  
    
        mul_su = {{ N {sa[N]}}, sa}*{{ N {ub[N]}}, ub};
    endfunction

    // RISC-V DIV/REM semantics (RV32M), including corner cases
    function automatic [N-1:0] rv32_div_q(input logic [N-1:0] a, b, input bit signed_op);
        if (b == {N{1'd0}})                      rv32_div_q = signed_op ? ALL1 : ALL1; // -1 == 0xFFFF_FFFF
        else if (signed_op && (a==INT_MIN) && (b==ALL1)) rv32_div_q = INT_MIN; // overflow
        else if (signed_op)                  rv32_div_q = $signed(a) / $signed(b);
        else                                 rv32_div_q = $unsigned(a) / $unsigned(b);
    endfunction

    function automatic [N-1:0] rv32_div_r(input logic [N-1:0] a, b, input bit signed_op);
        if (b == {N{1'd0}})                      rv32_div_r = a;         // remainder = dividend
        else if (signed_op && (a==INT_MIN) && (b==ALL1)) rv32_div_r = {N{1'd0}}; // overflow
        else if (signed_op)                  rv32_div_r = $signed(a) % $signed(b);
        else                                 rv32_div_r = $unsigned(a) % $unsigned(b);
    endfunction


    // Bind to DUT ports
    // (Formal tools let you refer to the bound instance?s signals by name)
    wire         valid_i       ;
    wire         inst_mul_i    ;
    wire         inst_mulh_i   ;
    wire         inst_mulhsu_i ;
    wire         inst_mulhu_i  ;
    wire         inst_div_i    ;
    wire         inst_divu_i   ;
    wire         inst_rem_i    ;
    wire         inst_remu_i   ;

    wire [N-1:0]  operand_ra_i  ;
    wire [N-1:0]  operand_rb_i  ;

    wire         stall_o       ;
    wire         ready_o       ;
    wire [N-1:0]  result_o      ;

    uriscv_muldiv_param DUT (.*);

    // --------- Decodes & starts ----------
    wire mul_dec = inst_mul_i | inst_mulh_i | inst_mulhsu_i | inst_mulhu_i;
    wire div_dec = inst_div_i | inst_divu_i | inst_rem_i | inst_remu_i;
    wire any_dec = mul_dec | div_dec;

    // A "start" is when the DUT is being presented an op the block may accept.
    // Note: the DUT latches MUL even if stall_o=1, but protocol-wise, producers should obey stall.
    wire start   = valid_i & any_dec & ~stall_o;
    wire start_mul = start & mul_dec;
    wire start_div = start & div_dec;

    // ---------- ENVIRONMENT ASSUMPTIONS ----------
    // Exactly one op bit when valid (or none if valid=0). Prevents illegal mixes.
    assume_onehot_ops: assume property (@(posedge clk_i) disable iff (rst_i)
        valid_i |-> $onehot({inst_mul_i,inst_mulh_i,inst_mulhsu_i,inst_mulhu_i,
                            inst_div_i,inst_divu_i,inst_rem_i,inst_remu_i}));

    assume_onehot_opss: assume property (@(posedge clk_i) disable iff (rst_i)
        !valid_i |-> ({inst_mul_i,inst_mulh_i,inst_mulhsu_i,inst_mulhu_i,
                            inst_div_i,inst_divu_i,inst_rem_i,inst_remu_i} == 0 ));
    // Producer must either (a) not assert valid when stalled, or (b) hold inputs stable while stalled.
    // Pick behavior by STRICT_ENV:
 
    assume_no_valid_while_stalled: assume property (@(posedge clk_i) disable iff (rst_i)
        stall_o |-> !valid_i);
    
    assume_valid_is_a_pulse: assume property (@(posedge clk_i) disable iff (rst_i)
        valid_i |=> !valid_i[*1:$] ##0 ready_o);
    
        


    property a_mul_lo;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_mul_i, expected = mul_uu(operand_ra_i, operand_rb_i)[N-1:0]) 
        ##1 (!ready_o)[*0:$]##1 ready_o
        |-> (result_o == expected)   );

    endproperty

    assert property (a_mul_lo);

    property a_mulh_ss;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_mulh_i, expected = mul_ss(operand_ra_i, operand_rb_i)[2*N-1:N]) ##1 (!ready_o)[*0:$]##1 ready_o 
           |-> (result_o == expected)   );

    endproperty

    assert property (a_mulh_ss);

    property a_mulhsu;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_mulhsu_i, expected = mul_su(operand_ra_i, operand_rb_i)[2*N-1:N]) ##1 (!ready_o)[*0:$]##1 ready_o
           |-> (result_o == expected)   );
    endproperty

    assert property (a_mulhsu);

    property a_mulhu;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_mulhu_i, expected = mul_uu(operand_ra_i, operand_rb_i)[2*N-1:N]) ##1 (!ready_o)[*0:$]##1 ready_o
           |-> (result_o == expected)   );

    endproperty

    assert property (a_mulhu);

    property a_div_q_signed;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_div_i, expected = rv32_div_q(operand_ra_i, operand_rb_i, 1'b1)) ##1 (!ready_o)[*0:$]##1 ready_o
           |-> (result_o == expected)   );

    endproperty

    assert property (a_div_q_signed);

    property a_div_q_unsigned;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_divu_i, expected = rv32_div_q(operand_ra_i, operand_rb_i, 1'b0)) ##1 (!ready_o)[*0:$]##1 ready_o
           |-> (result_o == expected)   );

    endproperty

    assert property (a_div_q_unsigned);

    property a_rem_r_signed;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_rem_i, expected = rv32_div_r(operand_ra_i, operand_rb_i, 1'b1)) ##1 (!ready_o)[*0:$]##1 ready_o
           |-> (result_o == expected)   );

    endproperty

    assert property (a_rem_r_signed);

    property a_rem_r_unsigned;
        logic [N-1:0] expected;
        @(posedge clk_i) disable iff (rst_i)
        ( (start && inst_remu_i, expected = rv32_div_r(operand_ra_i, operand_rb_i, 1'b0)) ##1 (!ready_o)[*0:$]##1 ready_o
           |-> (result_o == expected)   );

    endproperty

    assert property (a_rem_r_unsigned);

  

    // // ---------- COVERAGE ----------
    // c_mulh_negpos: cover property (@(posedge clk_i) disable iff (rst_i)
    // start && inst_mulh_i && operand_ra_i[31] && !operand_rb_i[31] ##1 ready_o);

    // c_div_by_zero: cover property (@(posedge clk_i) disable iff (rst_i)
    // start && (inst_div_i || inst_divu_i || inst_rem_i || inst_remu_i) && (operand_rb_i==32'd0)
    // ##32 ready_o);

    // c_div_overflow: cover property (@(posedge clk_i) disable iff (rst_i)
    // start && inst_div_i && (operand_ra_i == INT_MIN) && (operand_rb_i == 32'hFFFF_FFFF)
    // ##32 ready_o);

endmodule

// Bind into the DUT (in your tb or a bind file)
// bind uriscv_muldiv uriscv_muldiv_sva u_muldiv_sva(.clk_i(clk_i), .rst_i(rst_i));
