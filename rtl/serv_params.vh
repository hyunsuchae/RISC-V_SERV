localparam [0:0]
  OFFSET_SOURCE_IMM = 1'd0,
  OFFSET_SOURCE_RS1 = 1'd1;

localparam [0:0]
  OP_B_SOURCE_IMM = 1'd0,
  OP_B_SOURCE_RS2 = 1'd1;

localparam[1:0]
  ALU_RESULT_ADD  = 2'd0,
  ALU_RESULT_SR   = 2'd1,
  ALU_RESULT_LT   = 2'd2,
  ALU_RESULT_BOOL = 2'd3;

localparam [0:0]
  ALU_CMP_LT = 1'b0,
  ALU_CMP_EQ = 1'b1;

/*
 source
 ADD, SUB
 SL,SR
 SLT
 XOR,
 OR
 AND
*/

localparam [1:0]
  CSR_SOURCE_CSR = 2'b00,
  CSR_SOURCE_EXT = 2'b01,
  CSR_SOURCE_SET = 2'b10,
  CSR_SOURCE_CLR = 2'b11;
