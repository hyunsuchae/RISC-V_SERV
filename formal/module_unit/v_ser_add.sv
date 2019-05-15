

module v_ser_add(
	input clk,
	input rst,
	input a,
	input b,
	input clr,
	input q,
	input o_v
);

//ASSUME


//ASSERT
// when clr==1, carry-in is zero
	clr1_ov_check: assert property (@(posedge clk) disable iff(rst) clr |=> (o_v == (a&&b)));
	clr1_q_check: assert property (@(posedge clk) disable iff(rst) clr |=> (q == (a^b)));

//reset
//	rst_check: assert property (@(posedge clk) $fell(rst) |-> $past( (q==1'b0) && (o_v == 1'b0),1));

// disable rst and clr, check o_v and q depending on carry-in
	ov1_ov_check: assert property (@(posedge clk) disable iff(rst || clr ) o_v |=> (o_v == (a || b)));	
	ov0_ov_check: assert property (@(posedge clk) disable iff(rst || clr ) ~o_v |=> (o_v == (a && b)));
	
	ov1_q_check: assert property (@(posedge clk) disable iff(rst || clr) o_v |=> (q == ~(a^b)));	
	ov0_q_check: assert property (@(posedge clk) disable iff(rst || clr) ~o_v |=> (q == (a^b)));	

endmodule

module Wrapper;

bind ser_add v_ser_add v_ser_add_inst(
	.clk(clk),
	.rst(rst),
	.a(a),
	.b(b),
	.clr(clr),
	.q(q),
	.o_v(o_v)
);
endmodule
