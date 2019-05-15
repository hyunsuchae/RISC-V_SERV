

module v_serv_alu(
   input     clk,
   input     i_rst,
   input     i_en,
   input     i_rs1,
   input     i_op_b,
   input     i_buf,
   input     i_init,
   input     i_cnt_done,
   input     i_sub,
   input [1:0] i_bool_op,
   input     i_cmp_sel,
   input     i_cmp_neg,
   input     i_cmp_uns,

   input    i_shamt_en,
   input    i_sh_right,
   input    i_sh_signed,

   input [1:0] i_rd_sel,

   input    o_cmp,
   input    o_sh_done,
   input    o_rd,

   input    result_add,
   input    result_sh,
   input    result_lt_r

);

//ASSUME


//ASSERT

//for bolean operation
bool_xor: assert property (@(posedge clk) disable iff (i_rst) (i_bool_op == 2'b00) && (i_rd_sel == 2'b11) |->  (i_rs1^i_op_b) == o_rd );
bool_or: assert property (@(posedge clk) disable iff (i_rst) (i_bool_op == 2'b10) && (i_rd_sel == 2'b11) |->  (i_rs1|i_op_b) == o_rd );
bool_and: assert property (@(posedge clk) disable iff (i_rst) (i_bool_op == 2'b11) && (i_rd_sel == 2'b11) |->  (i_rs1&i_op_b) == o_rd );

//check result
add_result: assert property (@(posedge clk) disable iff (i_rst) (i_rd_sel == 2'b00) |->  result_add == o_rd );
sh_result: assert property (@(posedge clk) disable iff (i_rst)  (i_rd_sel == 2'b01) |->  result_sh == o_rd );
lt_result: assert property (@(posedge clk) disable iff (i_rst)  (i_rd_sel == 2'b10) |->  result_lt_r == o_rd );



//COVER

endmodule

module Wrapper;

bind serv_alu v_serv_alu v_serv_alu_inst(
    .clk       (clk),
    .i_rst     (i_rst),
    .i_en      (i_en),
    .i_rs1     (i_rs1),
    .i_op_b    (i_op_b),
    .i_buf     (i_buf),
    .i_init    (i_init),
    .i_cnt_done(i_cnt_done),
    .i_sub     (i_sub),
    .i_bool_op (i_bool_op),
    .i_cmp_sel (i_cmp_sel),
    .i_cmp_neg (i_cmp_neg),
    .i_cmp_uns (i_cmp_uns),
                           
    .i_shamt_en(i_shamt_en),
    .i_sh_right(i_sh_right),
    .i_sh_signed(i_sh_signed),
                           
    .i_rd_sel  (i_rd_sel),
                           
    .o_cmp     (o_cmp),
    .o_sh_done (o_sh_done),
    .o_rd      (o_rd),

    .result_add (result_add),         
    .result_sh (result_sh),
    .result_lt (result_lt_r)


);
endmodule
