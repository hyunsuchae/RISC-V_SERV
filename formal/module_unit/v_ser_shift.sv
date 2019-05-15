

module v_ser_shift(
	input i_clk,
	input i_rst,
	input i_load,
	input [4:0] i_shamt,
	input i_shamt_msb,
	input i_signbit,
	input i_right,
	input i_d,

	input o_done,
	input o_q
);

//ASSUME



//ASSERT
check_shamt_00: assert property ( @(posedge i_clk) disable iff(i_rst) (i_shamt == 0) && (i_d == 0) && $rose(i_load) |-> o_q);

check_shamt_32: assert property ( @(posedge i_clk) disable iff(i_rst) (i_shamt == 5'b10000)&&(~i_right) |=> (o_q==0));


//actual right shift





//COVER

check_q: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) ~i_right |-> i_signbit);
check_q2: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) ~i_right |=> i_signbit);

check_q3: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) i_right |-> i_signbit);
check_q4: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) i_right |=> i_signbit);

check_q5: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) ~i_right |-> ~i_signbit);
check_q6: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) ~i_right |=> ~i_signbit);

check_q7: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) i_right |-> ~i_signbit);
check_q8: cover property (@(posedge i_clk) disable iff(i_rst||~i_load) i_right |=> ~i_signbit);

endmodule

module Wrapper;

bind ser_shift v_ser_shift v_ser_shift_inst(
	.i_clk(i_clk),
	.i_rst(i_rst),
	.i_load(i_load),
	.i_shamt(i_shamt),
	.i_shamt_msb(i_shamt_msb),
	.i_signbit(i_signbit),
	.i_right(i_right),
	.i_d(i_d),

	.o_done(o_done),
	.o_q(o_q)
);
endmodule
