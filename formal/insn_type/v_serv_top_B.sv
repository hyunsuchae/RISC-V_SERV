

module v_serv_top(
	input clk,
	input i_rst,
	input i_timer_irq,
	input [31:0] i_ibus_rdt,
	input 	i_ibus_ack,
	input [31:0] i_dbus_rdt,
	input 	i_dbus_ack,

	input  	      rvfi_valid,
   	input [63:0]  rvfi_order,
   	input [31:0]  rvfi_insn,
   	input         rvfi_trap,
   	input         rvfi_halt,
   	input         rvfi_intr,
   	input [1:0]   rvfi_mode,
   	input [4:0]   rvfi_rs1_addr,
   	input [4:0]   rvfi_rs2_addr,
   	input [31:0]  rvfi_rs1_rdata,
   	input [31:0]  rvfi_rs2_rdata,
   	input [4:0]   rvfi_rd_addr,
   	input [31:0]  rvfi_rd_wdata,
   	input [31:0]  rvfi_pc_rdata,
   	input [31:0]  rvfi_pc_wdata,
   	input [31:0]  rvfi_mem_addr,
   	input [3:0]   rvfi_mem_rmask,
   	input [3:0]   rvfi_mem_wmask,
   	input [31:0]  rvfi_mem_rdata,
   	input [31:0]  rvfi_mem_wdata,

   	input [31:0]  o_ibus_adr,
   	input         o_ibus_cyc,

   	input [31:0]  o_dbus_adr,
   	input [31:0]  o_dbus_dat,
   	input [3:0]   o_dbus_sel,
   	input         o_dbus_we ,
   	input         o_dbus_cyc,

	input [31:0] pc
);

//****************************************ASSUME*********************************************//
	// for instruction-MEM
	always @(posedge clk) begin
		if (!o_ibus_cyc) begin
			assume (!i_ibus_ack);
		end
	end

	// for data-MEM
	always @(posedge clk) begin
		if (!o_dbus_cyc) begin
			assume (!i_dbus_ack);
		end
	end

  	wire [4:0] B_opcode 	= rvfi_insn[ 6: 2];
  	wire [2:0] B_funct3 	= rvfi_insn[14:12];

  	wire [4:0] B_rs2  	= rvfi_insn[24:20];
 	wire [4:0] B_rs1  	= rvfi_insn[19:15];
  	wire [31:0] B_imm 	= $signed({rvfi_insn[31], rvfi_insn[7], rvfi_insn[30:25], rvfi_insn[11:8], 1'b0 });


	B_opcode_assume: assume property (@(posedge clk) disable iff(i_rst) (B_opcode == 5'b11000));
	B_funct3_assume: assume property (@(posedge clk) disable iff(i_rst)  (B_funct3 == 3'b000));
	B_op21_assume: assume property (@(posedge clk) disable iff(i_rst) (rvfi_insn[21] == 1));
	B_pc_assume: assume property (@(posedge clk) disable iff(i_rst) (rvfi_pc_rdata != 0) && (rvfi_pc_rdata[1:0] == 0));

	B_regs_assume: assume property (@(posedge clk) disable iff(i_rst) (B_rs2 !== 0) && (B_rs1 !== 0));



//*****************************************ASSERT******************************************//

	wire [31:0] take_next_pc = rvfi_pc_rdata + B_imm;
	wire [31:0] not_take_next_pc = rvfi_pc_rdata + 4;

/*	reg [1:0] start;

	
	always @(posedge clk) begin
		if(i_rst)  start <=2;
		else begin
			if(rvfi_valid && rvfi_trap) start <= 0 ;
			else if(rvfi_valid && ~rvfi_trap) begin
				if( start < 2'b11) start <= start + 1;	
				else start <= start;
			end
		end
	end
	
*/

	check_BEQ_take: assert property (@(posedge clk) disable iff(i_rst) (rvfi_valid) && (rvfi_trap == 0)
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b000)  
					&& (rvfi_rs1_rdata == rvfi_rs2_rdata)   
					|-> (rvfi_pc_wdata == take_next_pc) );

	check_BEQ_not_take: assert property (@(posedge clk) disable iff(i_rst) (rvfi_valid) && (rvfi_trap == 0)
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b000) 
					&& (rvfi_rs1_rdata != rvfi_rs2_rdata)
					|-> (rvfi_pc_wdata == not_take_next_pc) );
/*

	check_BNE_take: assert property (@(posedge clk) disable iff(i_rst) (rvfi_valid) 
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b001) 
					&& (rvfi_rs1_rdata != rvfi_rs2_rdata) 
					|-> (rvfi_pc_wdata == take_next_pc) );

	check_BNE_not_take: assert property (@(posedge clk) disable iff(i_rst) (rvfi_valid) 
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b001) 
					&& (rvfi_rs1_rdata == rvfi_rs2_rdata) 
					|=> (rvfi_pc_wdata == not_take_next_pc) );


	check_BLT_take: assert property (@(posedge clk) disable iff(i_rst) (rvfi_valid) 
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b100)
					&& ($signed(rvfi_rs1_rdata) < $signed(rvfi_rs2_rdata)) && (rvfi_pc_wdata != RESET_PC + B_imm)
					|-> (rvfi_pc_wdata == take_next_pc) );

	check_BLT_not_take: assert property (@(posedge clk) disable iff(i_rst) (rvfi_valid) 
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b100) 
					&& ($signed(rvfi_rs1_rdata) >= $signed(rvfi_rs2_rdata)) && (rvfi_pc_wdata != RESET_PC + 4)
					|=> (rvfi_pc_wdata == not_take_next_pc) );


 
	check_BGE_take: assert property (@(posedge clk) disable iff(i_rst)
					(rvfi_valid) && (rvfi_trap == 0)
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b101) && ( $signed(rvfi_rs1_rdata) > $signed(rvfi_rs2_rdata))
					|-> (rvfi_pc_wdata == (rvfi_pc_rdata + B_imm)) ); 
	check_BLTU_take: assert property (@(posedge clk) disable iff(i_rst)
					(rvfi_valid) && (rvfi_trap == 0)
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b110) && (rvfi_rs1_rdata < rvfi_rs2_rdata)
					|-> (rvfi_pc_wdata == (rvfi_pc_rdata + B_imm)) ); 
	check_BGEU_take: assert property (@(posedge clk) disable iff(i_rst)
					(rvfi_valid) && (rvfi_trap == 0)
					&&(B_opcode == 5'b11000) && (B_funct3 == 3'b111) && (rvfi_rs1_rdata < rvfi_rs2_rdata)
					|-> (rvfi_pc_wdata == (rvfi_pc_rdata + B_imm)) ); 

*/





//COVER


endmodule

module Wrapper;

bind serv_top v_serv_top v_serv_top_inst(

	.clk(clk),         
	.i_rst(i_rst),
	.i_timer_irq(i_timer_irq),
	.i_ibus_rdt      (i_ibus_rdt),
	.i_ibus_ack     (i_ibus_ack),
	.i_dbus_rdt     (i_dbus_rdt),
	.i_dbus_ack     (i_dbus_ack),
                                       
	.rvfi_valid     (rvfi_valid),
   	.rvfi_order     (rvfi_order),
   	.rvfi_insn      (rvfi_insn),
   	.rvfi_trap      (rvfi_trap),
   	.rvfi_halt      (rvfi_halt),
   	.rvfi_intr      (rvfi_intr),
   	.rvfi_mode      (rvfi_mode),
   	.rvfi_rs1_addr  (rvfi_rs1_addr),
   	.rvfi_rs2_addr  (rvfi_rs2_addr),
   	.rvfi_rs1_rdata (rvfi_rs1_rdata),
   	.rvfi_rs2_rdata (rvfi_rs2_rdata),
   	.rvfi_rd_addr   (rvfi_rd_addr),
   	.rvfi_rd_wdata  (rvfi_rd_wdata),
   	.rvfi_pc_rdata  (rvfi_pc_rdata),
   	.rvfi_pc_wdata  (rvfi_pc_wdata),
   	.rvfi_mem_addr  (rvfi_mem_addr),
   	.rvfi_mem_rmask (rvfi_mem_rmask),
   	.rvfi_mem_wmask (rvfi_mem_wmask),
   	.rvfi_mem_rdata (rvfi_mem_rdata),
   	.rvfi_mem_wdata (rvfi_mem_wdata),
   	.o_ibus_adr     (o_ibus_adr),
   	.o_ibus_cyc     (o_ibus_cyc),
   	.o_dbus_adr     (o_dbus_adr),
   	.o_dbus_dat     (o_dbus_dat),
   	.o_dbus_sel     (o_dbus_sel),
   	.o_dbus_we      (o_dbus_we) ,
   	.o_dbus_cyc     (o_dbus_cyc),
	.pc		(pc)
);
endmodule
