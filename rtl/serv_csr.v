`default_nettype none
module serv_csr
  (
   input wire 	    i_clk,
   input wire [4:0] i_cnt,
   input wire [3:0] i_cnt_r,
   input wire 	    i_mtip,
   output wire 	    o_timer_irq_en,
   input wire 	    i_mstatus_en,
   input wire 	    i_mie_en,
   input wire 	    i_mtvec_en,
   input wire 	    i_mip_en,
   input wire 	    i_mscratch_en,
   input wire 	    i_mepc_en,
   input wire 	    i_mcause_en,
   input wire 	    i_mtval_en,
   input wire [1:0] i_csr_source,
   input wire 	    i_trap,
   input wire 	    i_pc,
   input wire 	    i_mtval,
   input wire [3:0] i_mcause,
   input wire 	    i_d,
   output wire 	    o_q);

`include "serv_params.vh"
   /*
    300 mstatus RWSC
    304 mie SCWi
    305 mtvec RW
    344 mip CWi

    340 mscratch
    341 mepc  RW
    342 mcause R
    343 mtval
    */

   reg 		    mstatus;
   reg 		    mstatus_mie;
   reg 		    mie_mtie;
   reg [31:0] 	    mtvec    = 32'h0;

   reg [31:0] 	mscratch;
   reg [31:0] 	mepc;
   reg 		mcause31;
   reg [3:0] 	mcause3_0;
   wire 	mcause;
   reg [31:0] 	mtval;


   wire 	csr_in;
   wire 	csr_out;

   assign csr_in = (i_csr_source == CSR_SOURCE_EXT) ? i_d :
		   (i_csr_source == CSR_SOURCE_SET) ? csr_out | i_d :
		   (i_csr_source == CSR_SOURCE_CLR) ? csr_out & ~i_d :
		   (i_csr_source == CSR_SOURCE_CSR) ? csr_out :
		   1'bx;

   assign csr_out = (i_mstatus_en & mstatus) |
		    (i_mtvec_en & mtvec[0]) |
		    (i_mscratch_en & mscratch[0]) |
		    (i_mepc_en & mepc[0]) |
		    (i_mcause_en & mcause) |
		    (i_mtval_en & mtval[0]);

   assign o_q = csr_out;

   assign 	o_timer_irq_en = mstatus_mie & mie_mtie;

   assign mcause = (i_cnt[4:2] == 3'd0) ? mcause3_0[0] : //[3:0]
		   ((i_cnt[4:2] == 3'd7) & i_cnt_r[3]) ? mcause31 //[31]
		   : 1'b0;

   always @(posedge i_clk) begin
      if (i_mstatus_en & (i_cnt[4:2] == 3'd0) & i_cnt_r[3])
	mstatus_mie <= csr_in;

      if (i_mie_en & (i_cnt[4:2] == 3'd1) & i_cnt_r[3])
	mie_mtie <= csr_in;

      mstatus <= (i_cnt[4:2] == 0) & i_cnt_r[2] & mstatus_mie;

      if (i_trap) begin
	 mcause31  <= i_mtip & o_timer_irq_en;
	 mcause3_0 <= (i_mtip & o_timer_irq_en) ? 4'd7 : i_mcause[3:0];
      end
      if (i_mscratch_en)
	mscratch <= {csr_in, mscratch[31:1]};

      if (i_mtvec_en)
	mtvec <= {csr_in, mtvec[31:1]};

      if (i_mepc_en | i_trap)
	mepc <= {i_trap ? i_pc : csr_in, mepc[31:1]};

      if (i_mcause_en) begin
	 if (i_cnt[4:2] == 3'd0)
	   mcause3_0 <= {csr_in, mcause3_0[3:1]};
	 if ((i_cnt[4:2] == 3'd7) & i_cnt_r[3])
	   mcause31 <= csr_in;
      end

      if (i_mtval_en | i_trap)
	mtval <= {i_trap ? i_mtval : csr_in, mtval[31:1]};
   end

endmodule
