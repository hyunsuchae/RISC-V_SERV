

module v_ser_lt(
	input i_clk,
	input i_a,
	input i_b,
	input i_clr,
	input i_sign,
	output o_q
);




endmodule

module Wrapper_ser_lt;

bind ser_lt v_ser_lt v_ser_lt_inst(
	.i_clk(i_clk),
	.i_a(i_a),
	.i_b(i_b),
	.i_clr(i_clr),
	.i_sign(i_sign),
	.o_q(o_q)
);
endmodule
