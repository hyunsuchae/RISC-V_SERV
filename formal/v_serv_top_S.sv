

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


	// common parameters for both store and load
  	wire [4:0] opcode = rvfi_insn[ 6: 2];
  	wire [2:0] funct3 = rvfi_insn[14:12];
  	wire [4:0] rs1_adr= rvfi_insn[19:15];

	// store
  	wire [4:0] S_rs2_adr = rvfi_insn[24:20];
  	wire [11:0] S_imm    = {rvfi_insn[31:25], rvfi_insn[11:7]};
	// load
  	wire [4:0] L_rd_adr  = rvfi_insn[11:7];
  	wire [11:0] L_imm    = rvfi_insn[31:20];

	// expected memory address
	wire [31:0] L_memaddr = $signed(rvfi_rs1_rdata) + $signed(L_imm);
	wire [31:0] S_memaddr = $signed(rvfi_rs1_rdata) + $signed(S_imm);


	assume_SWLW: assume property (@(posedge clk) disable iff(i_rst) 
					(  (opcode==5'b00000 && funct3==3'b010 && L_memaddr[1:0]==2'b0 && L_memaddr<32'h80000000)
					|| (opcode==5'b01000 && funct3==3'b010 && S_memaddr[1:0]==2'b0 && S_memaddr<32'h80000000)
					) && (rvfi_rs1_rdata[31] == 0) && rvfi_trap == 0	);

//*****************************************ASSERT******************************************//

//SW: M[rs1 + imm] <- rs2
//LW: rd <- M[rs1+imm]

	check_LW_addr: assert property (@(posedge clk) disable iff(i_rst) rvfi_valid && (rvfi_trap == 0)
					&& (opcode == 5'b00000) && (funct3 == 3'b010) && (o_dbus_we==0)	
					|-> (L_memaddr == rvfi_mem_addr));

	check_SW_addr: assert property (@(posedge clk) disable iff(i_rst) rvfi_valid && (rvfi_trap==0) 	
					&& (opcode==5'b01000) && (funct3==3'b010) && (o_dbus_we==1) 
					|-> (S_memaddr == rvfi_mem_addr));
/*	check_SW_data: assert property (@(posedge clk) disable iff(i_rst) rvfi_valid && (rvfi_trap==0) 
					&& (opcode==5'b01000) && (funct3==3'b010) && (o_dbus_we==1) 
					|-> (rvfi_rs2_rdata == rvfi_mem_wdata));
*/



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
