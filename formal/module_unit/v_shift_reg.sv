

module v_shift_reg(
	input clk,
	input i_rst,
	input i_en,
	input i_d,

	input o_q
	input [3:0] o_par,
);

//ASSUME



//ASSERT




//COVER


endmodule

module Wrapper;

bind shift_reg v_shift_reg v_shift_reg_inst(
	.clk(clk),
	.i_rst(i_rst),
	.i_en(i_en),
	.i_d(i_d),

	.o_q(o_q)
	.o_par(o_par),
);
endmodule
