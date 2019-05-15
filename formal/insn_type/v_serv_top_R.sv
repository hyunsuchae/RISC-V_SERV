

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
   	input         o_dbus_cyc
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

  	wire [4:0] R_opcode 	= rvfi_insn[ 6: 2];
  	wire [6:0] R_funct7 	= rvfi_insn[31:25];
  	wire [2:0] R_funct3 	= rvfi_insn[14:12];
  	wire [4:0] R_rs2    	= rvfi_insn[24:20];
  	wire [4:0] R_rs1    	= rvfi_insn[19:15];
  	wire [4:0] R_rd     	= rvfi_insn[11: 7];

	assume_regs: assume property (@(posedge clk) disable iff(i_rst) (R_rs2 !== 0) && (R_rs1 !== 0));

	assume_R_opcode: assume property (@(posedge clk) disable iff(i_rst) (R_opcode == 5'b01100));

	assume_R_funct7: assume property (@(posedge clk) disable iff(i_rst) (R_funct7[0] == 0));

//*****************************************ASSERT******************************************//

///////////////////////////R types//////////////////////////
	check_AND: assert property (@(posedge clk) disable iff(i_rst) 
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&& (R_opcode == 5'b01100) && (R_funct3 == 3'b111)
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata & rvfi_rs2_rdata)));
	check_OR: assert property (@(posedge clk) disable iff(i_rst) 
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b110)
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata | rvfi_rs2_rdata)));
	check_XOR: assert property (@(posedge clk) disable iff(i_rst) 
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b100)
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata ^ rvfi_rs2_rdata)));
	check_ADD: assert property (@(posedge clk) disable iff(i_rst) 
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b000) && (R_funct7[5] == 0) 
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata + rvfi_rs2_rdata)));
	check_SUB: assert property (@(posedge clk) disable iff(i_rst) 
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b000) && (R_funct7[5] == 1) 
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata - rvfi_rs2_rdata)));

	check_SLL: assert property (@(posedge clk) disable iff(i_rst) 					// shift left logical
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b001)
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata << rvfi_rs2_rdata[4:0])));
	check_SRL: assert property (@(posedge clk) disable iff(i_rst) 					// shift right logical
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b101) && (R_funct7[5] == 0)
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata >> rvfi_rs2_rdata[4:0])));

	check_SLT: assert property (@(posedge clk) disable iff(i_rst) 					// set less than
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b010)
				 	|-> (rvfi_rd_wdata== ( $signed(rvfi_rs1_rdata) < $signed(rvfi_rs2_rdata) )));
	check_SLTU: assert property (@(posedge clk) disable iff(i_rst) 					//set less than unsigned
					(rvfi_valid) && (R_rd!==0) && (rvfi_trap == 0)
 					&&(R_opcode == 5'b01100) && (R_funct3 == 3'b011)
				 	|-> (rvfi_rd_wdata== (rvfi_rs1_rdata < rvfi_rs2_rdata)));

	



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
   	.o_dbus_cyc     (o_dbus_cyc)
);
endmodule
