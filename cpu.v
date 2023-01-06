`define ADDR_W 64
`define DATA_W 64
`define INST_W 32
module cpu #( // Do not modify interface
	parameter ADDR_W = 64,
	parameter INST_W = 32,
	parameter DATA_W = 64
)(
    input                   i_clk,
    input                   i_rst_n,
    input                   i_i_valid_inst, // from instruction memory
    input  [ INST_W-1 : 0 ] i_i_inst,       // from instruction memory
    input                   i_d_valid_data, // from data memory
    input  [ DATA_W-1 : 0 ] i_d_data,       // from data memory
    output                  o_i_valid_addr, // to instruction memory
    output [ ADDR_W-1 : 0 ] o_i_addr,       // to instruction memory
    output [ DATA_W-1 : 0 ] o_d_w_data,     // to data memory
    output [ ADDR_W-1 : 0 ] o_d_w_addr,     // to data memory
    output [ ADDR_W-1 : 0 ] o_d_r_addr,     // to data memory
    output                  o_d_MemRead,    // to data memory
    output                  o_d_MemWrite,   // to data memory
    output                  o_finish
);
    wire [`INST_W-1:0] IF_inst;
    wire         [7:0] IF_inst_addr;

    wire [`INST_W-1:0] ID_inst;
    wire         [7:0] ID_inst_addr;
    wire         [4:0] ID_rs1;
    wire         [4:0] ID_rs2;
    wire         [4:0] ID_rd;
    wire [`DATA_W-1:0] ID_read_data1;
    wire [`DATA_W-1:0] ID_read_data2;
    wire [`DATA_W-1:0] ID_immediate;
    wire         [6:0] ID_opcode;
    wire         [2:0] ID_funct3;
    wire         [6:0] ID_funct7;
    wire         [2:0] ID_ALU_op;
    wire               ID_valid_rs2;
    wire               ID_write_flag;
    wire               ID_MemRead;
    wire               ID_MemWrite;
    wire               ID_RegWrite;
    wire               ID_ALU_src;
    wire         [1:0] ID_branch;
    wire               ID_finish;

    wire         [4:0] EX_rs1;
    wire         [4:0] EX_rs2;
    wire         [4:0] EX_rd;
    wire [`DATA_W-1:0] EX_read_data1;
    wire [`DATA_W-1:0] EX_read_data2;
    wire [`DATA_W-1:0] EX_immediate;
    wire [`DATA_W-1:0] EX_ALU_src_data;
    wire [`DATA_W-1:0] EX_store_data;
    wire         [7:0] EX_inst_addr;
    wire [`DATA_W-1:0] EX_ALU_input1;
    wire [`DATA_W-1:0] EX_ALU_input2;
    wire [`DATA_W-1:0] EX_ALU_result;
    wire         [2:0] EX_ALU_op;
    wire               EX_valid_rs2;
    wire               EX_write_flag;
    wire               EX_MemRead;
    wire               EX_MemWrite;
    wire               EX_RegWrite;
    wire               EX_ALU_src;
    wire         [1:0] EX_branch;
    wire               EX_finish;

    wire         [4:0] MEM_rd;
    wire [`DATA_W-1:0] MEM_ALU_result;
    wire [`DATA_W-1:0] MEM_store_data;
    wire [`DATA_W-1:0] MEM_MEM_result;
    wire               MEM_write_flag;
    wire               MEM_MemRead;
    wire               MEM_MemWrite;
    wire               MEM_RegWrite;
    wire               MEM_finish;

    wire         [4:0] WB_rd;
    wire [`DATA_W-1:0] WB_ALU_result;
    wire [`DATA_W-1:0] WB_MEM_result;
    wire [`DATA_W-1:0] WB_write_data;
    wire               WB_MemRead;
    wire               WB_RegWrite;
    wire               WB_finish;

    wire [7:0] PC_inst_addr;
    wire [7:0] PC_inst_addr_next;
    wire [7:0] PC_inst_addr_4;
    wire [7:0] PC_branch_target;
    wire       PC_branch, PC_flush;

    wire [1:0] forwardA, forwardB;

    assign PC_inst_addr_4 = PC_inst_addr + 4;
    assign PC_branch_target = EX_inst_addr + EX_immediate[7:0];

    MUX_PC mux_pc(PC_inst_addr_4, PC_branch_target, PC_branch, PC_inst_addr_next);
    PC pc(i_clk, i_rst_n, ~PC_flush, PC_inst_addr_next, PC_inst_addr);

    Forward_unit forward_unit(EX_valid_rs2, EX_rs1, EX_rs2, MEM_rd, MEM_RegWrite, WB_rd, WB_RegWrite, forwardA, forwardB);
    Hazard_unit hazard_unit(ID_rs1, ID_rs2, ID_valid_rs2, EX_rd, EX_MemRead, EX_ALU_input1, EX_ALU_input2, EX_branch, PC_flush, PC_branch);

    ID_pipeline ID_p(i_clk, i_rst_n, PC_branch, IF_inst, PC_inst_addr, ~PC_flush & ~PC_branch, ID_inst, ID_inst_addr, ID_write_flag);

    Registers regfile(~i_clk, i_rst_n, ID_rs1, ID_rs2, WB_rd, WB_RegWrite, WB_write_data, ID_read_data1, ID_read_data2);

    assign ID_rd     = ID_inst[11:7];
    assign ID_rs1    = ID_inst[19:15];
    assign ID_rs2    = ID_inst[24:20];
    assign ID_opcode = ID_inst[6:0];
    assign ID_funct3 = ID_inst[14:12];
    assign ID_funct7 = ID_inst[31:25];

    ImmGen immgen(ID_inst, ID_immediate);
    Control_unit control_unit(ID_opcode, ID_funct3, ID_valid_rs2, ID_MemRead, ID_MemWrite, ID_RegWrite, ID_ALU_src, ID_branch, ID_finish);
    ALU_control alu_control(ID_opcode, ID_funct3, ID_funct7, ID_ALU_op);

    EX_pipeline EX_p(i_clk, i_rst_n, ID_rs1, ID_rs2, ID_rd, ID_read_data1, ID_read_data2, ID_immediate, ID_inst_addr, ID_ALU_op, ID_write_flag & ~PC_flush & ~PC_branch, ID_valid_rs2, ID_MemRead, ID_MemWrite, ID_RegWrite, ID_ALU_src, ID_branch, ID_finish, EX_rs1, EX_rs2, EX_rd, EX_read_data1, EX_read_data2, EX_immediate, EX_inst_addr, EX_ALU_op, EX_write_flag, EX_valid_rs2, EX_MemRead, EX_MemWrite, EX_RegWrite, EX_ALU_src, EX_branch, EX_finish);

    MUX_2_1 mux_alu_src2(EX_read_data2, EX_immediate, EX_ALU_src, EX_ALU_src_data);
    MUX_4_1 mux_alu_input1(EX_read_data1, WB_write_data, MEM_ALU_result, 64'b0, forwardA, EX_ALU_input1);
    MUX_4_1 mux_alu_input2(EX_ALU_src_data, WB_write_data, MEM_ALU_result, 64'b0, (EX_MemWrite)? 2'b0: forwardB, EX_ALU_input2);
    MUX_4_1 mux_ex_store_data(EX_read_data2, WB_write_data, MEM_ALU_result, 64'b0, forwardB, EX_store_data);

    ALU alu(~i_clk, i_rst_n, EX_ALU_input1, EX_ALU_input2, EX_ALU_op, EX_ALU_result);

    MEM_pipeline MEM_p(i_clk, i_rst_n, EX_rd, EX_ALU_result, EX_store_data, EX_MemRead, EX_MemWrite, EX_RegWrite, EX_finish, MEM_rd, MEM_ALU_result, MEM_store_data, MEM_MemRead, MEM_MemWrite, MEM_RegWrite, MEM_finish);

    WB_pipeline WB_p(i_clk, i_rst_n, MEM_rd, MEM_ALU_result, MEM_MEM_result, MEM_MemRead, MEM_RegWrite, MEM_finish, WB_rd, WB_ALU_result, WB_MEM_result, WB_MemRead, WB_RegWrite, WB_finish);
    MUX_2_1 mux_wb_data(WB_ALU_result, WB_MEM_result, WB_MemRead, WB_write_data);

    assign IF_inst = (i_i_valid_inst)? i_i_inst: 0;

    assign MEM_MEM_result = (i_d_valid_data)? i_d_data: 0;

    assign o_i_addr = PC_inst_addr;
    assign o_i_valid_addr = ~PC_flush;

    assign o_d_MemRead  = MEM_MemRead;
    assign o_d_MemWrite = MEM_MemWrite;
    assign o_d_r_addr   = MEM_ALU_result;
    assign o_d_w_addr   = MEM_ALU_result;
    assign o_d_w_data   = MEM_store_data;

    assign o_finish = WB_finish;
endmodule

module PC(
    input        clk,
    input        rst_n,
    input        i_write_flag,
    input  [7:0] i_addr,
    output [7:0] o_addr
);
    reg [7:0] o_addr_r, o_addr_w;

    assign o_addr = o_addr_r;
    
    always @(*) begin
        o_addr_w = (i_write_flag)? i_addr: o_addr_r;
    end

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            o_addr_r <= 0;
        end
        else begin
            o_addr_r <= o_addr_w;
        end
    end
endmodule

module Registers(
    input                clk,
    input                rst_n,
    input          [4:0] rs1,
    input          [4:0] rs2,
    input          [4:0] rd,
    input                RegWrite,
    input  [`DATA_W-1:0] write_data,
    output [`DATA_W-1:0] read_data1,
    output [`DATA_W-1:0] read_data2
);  
    integer i;
    reg [`DATA_W-1:0] regs[31:0];
    reg [`DATA_W-1:0] regs_w[31:0];

    assign read_data1 = regs[rs1];
    assign read_data2 = regs[rs2];

    always @(*) begin
        for (i = 0; i < 32; i = i + 1) regs_w[i] = regs[i];
        if (RegWrite) regs_w[rd] = write_data;
    end

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            for (i = 0; i < 32; i = i + 1) regs[i] <= 0;
        end
        else begin
            for (i = 0; i < 32; i = i + 1) regs[i] <= regs_w[i];
        end
    end
endmodule

module ImmGen(
    input  [`INST_W-1:0] inst,
    output [`DATA_W-1:0] immediate
);
    assign immediate[63:12] = (inst[31])? ~0: 0;
    assign immediate[11:0]  = (inst[6:0] == 7'b0100011)? {{inst[31:25]}, {inst[11:7]}}:
                              (inst[6:0] == 7'b1100011)? {{inst[7]}, {inst[30:25]}, {inst[11:8]}, 1'b0}:
                              (inst[6:0] == 7'b0000011 || inst[6:0] == 7'b0010011)? {{inst[31:20]}}: 12'b0;
endmodule

module Control_unit(
    input  [6:0] opcode,
    input  [2:0] funct3,
    output       valid_rs2,
    output       MemRead,
    output       MemWrite,
    output       RegWrite,
    output       ALU_src,
    output [1:0] branch,
    output       finish
);
    assign valid_rs2 = (opcode == 7'b0100011) || (opcode == 7'b1100011) || (opcode == 7'b0110011);
    assign MemRead   = (opcode == 7'b0000011);
    assign MemWrite  = (opcode == 7'b0100011);
    assign RegWrite  = (opcode == 7'b0000011) || (opcode == 7'b0010011) || (opcode == 7'b0110011);
    assign ALU_src   = (opcode == 7'b0000011) || (opcode == 7'b0100011) || (opcode == 7'b0010011);
    assign branch    = (opcode == 7'b1100011)? ((funct3 == 3'b000)? 2'b01: 2'b10): 2'b00;
    assign finish    = (opcode == 7'b1111111);
endmodule

module Forward_unit(
    input        valid_rs2,
    input  [4:0] EX_rs1,
    input  [4:0] EX_rs2,
    input  [4:0] MEM_rd,
    input        MEM_RegWrite,
    input  [4:0] WB_rd,
    input        WB_RegWrite,
    output [1:0] forwardA,
    output [1:0] forwardB
);
    assign forwardA = ((EX_rs1 == MEM_rd) && (MEM_RegWrite))? 2'b10: 
                   ((EX_rs1 == WB_rd) && (WB_RegWrite))? 2'b01: 2'b00;
    assign forwardB = (valid_rs2 && (EX_rs2 == MEM_rd) && (MEM_RegWrite))? 2'b10:
                   (valid_rs2 && (EX_rs2 == WB_rd) && (WB_RegWrite))? 2'b01: 2'b00;
endmodule

module Hazard_unit(
    input         [4:0] ID_rs1,
    input         [4:0] ID_rs2,
    input               ID_valid_rs2,
    input         [4:0] EX_rd,
    input               EX_MemRead,
    input [`DATA_W-1:0] EX_data1,
    input [`DATA_W-1:0] EX_data2,
    input         [1:0] EX_branch,
    output              flush_flag,
    output              branch_flag
);
    assign flush_flag = ((ID_rs1 == EX_rd) && EX_MemRead) || (ID_valid_rs2 && (ID_rs2 == EX_rd) && EX_MemRead);
    assign branch_flag = ((EX_branch == 2'b01) && (EX_data1 == EX_data2)) || ((EX_branch == 2'b10) && (EX_data1 != EX_data2));
endmodule

module ID_pipeline(
    input                clk,
    input                rst_n,
    input                flush,
    input  [`INST_W-1:0] i_inst,
    input          [7:0] i_inst_addr,
    input                i_write_flag,
    output [`INST_W-1:0] o_inst, 
    output         [7:0] o_inst_addr,
    output               o_write_flag
);
    reg [`INST_W-1:0] o_inst_r, o_inst_w;
    reg         [7:0] o_inst_addr_r, o_inst_addr_w;
    reg               o_write_flag_r, o_write_flag_w;

    assign o_inst       = o_inst_r;
    assign o_inst_addr  = o_inst_addr_r;
    assign o_write_flag = o_write_flag_r;

    always @(*) begin
        if (flush) begin
            o_inst_w       = 0;
            o_inst_addr_w  = 0;
            o_write_flag_w = 0;            
        end
        else if (i_write_flag) begin
            o_inst_w       = i_inst;
            o_inst_addr_w  = i_inst_addr;
            o_write_flag_w = i_write_flag;
        end
        else begin
            o_inst_w       = o_inst_r;
            o_inst_addr_w  = o_inst_addr_r;
            o_write_flag_w = o_write_flag_r;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            o_inst_r       <= 0;
            o_inst_addr_r  <= 0;
            o_write_flag_r <= 0;
        end
        else begin
            o_inst_r       <= o_inst_w;
            o_inst_addr_r  <= o_inst_addr_w;
            o_write_flag_r <= o_write_flag_w;
        end
    end
endmodule

module EX_pipeline(
    input                clk,
    input                rst_n,
    input          [4:0] i_rs1,
    input          [4:0] i_rs2,
    input          [4:0] i_rd,
    input  [`DATA_W-1:0] i_read_data1,
    input  [`DATA_W-1:0] i_read_data2,
    input  [`DATA_W-1:0] i_immediate,
    input          [7:0] i_inst_addr,
    input          [2:0] i_ALU_op,
    input                i_write_flag,
    input                i_valid_rs2,
    input                i_MemRead,
    input                i_MemWrite,
    input                i_RegWrite,
    input                i_ALU_src,
    input          [1:0] i_branch,
    input                i_finish,
    output         [4:0] o_rs1,
    output         [4:0] o_rs2,
    output         [4:0] o_rd,
    output [`DATA_W-1:0] o_read_data1,
    output [`DATA_W-1:0] o_read_data2,
    output [`DATA_W-1:0] o_immediate,
    output         [7:0] o_inst_addr,
    output         [2:0] o_ALU_op,
    output               o_write_flag,
    output               o_valid_rs2,
    output               o_MemRead,
    output               o_MemWrite,
    output               o_RegWrite,
    output               o_ALU_src,
    output         [1:0] o_branch,
    output               o_finish
);
    reg         [4:0] o_rs1_r, o_rs1_w;
    reg         [4:0] o_rs2_r, o_rs2_w;
    reg         [4:0] o_rd_r, o_rd_w;
    reg [`DATA_W-1:0] o_read_data1_r, o_read_data1_w;
    reg [`DATA_W-1:0] o_read_data2_r, o_read_data2_w;
    reg [`DATA_W-1:0] o_immediate_r, o_immediate_w;
    reg         [7:0] o_inst_addr_r, o_inst_addr_w;
    reg         [2:0] o_ALU_op_r, o_ALU_op_w;
    reg               o_write_flag_r, o_write_flag_w;
    reg               o_valid_rs2_r, o_valid_rs2_w;
    reg               o_MemRead_r, o_MemRead_w;
    reg               o_MemWrite_r, o_MemWrite_w;
    reg               o_RegWrite_r, o_RegWrite_w;
    reg               o_ALU_src_r, o_ALU_src_w;
    reg         [1:0] o_branch_r, o_branch_w;
    reg               o_finish_r, o_finish_w;

    assign o_rs1        = o_rs1_r;
    assign o_rs2        = o_rs2_r;
    assign o_rd         = o_rd_r;
    assign o_read_data1 = o_read_data1_r;
    assign o_read_data2 = o_read_data2_r;
    assign o_immediate  = o_immediate_r;
    assign o_inst_addr  = o_inst_addr_r;
    assign o_ALU_op     = o_ALU_op_r;
    assign o_write_flag = o_write_flag_r;
    assign o_valid_rs2  = o_valid_rs2_r;
    assign o_MemRead    = o_MemRead_r;
    assign o_MemWrite   = o_MemWrite_r;
    assign o_RegWrite   = o_RegWrite_r;
    assign o_ALU_src    = o_ALU_src_r;
    assign o_branch     = o_branch_r;
    assign o_finish     = o_finish_r;

    always @(*) begin
        if (i_write_flag) begin
            o_rs1_w        = i_rs1;
            o_rs2_w        = i_rs2;
            o_rd_w         = i_rd;
            o_read_data1_w = i_read_data1;
            o_read_data2_w = i_read_data2;
            o_immediate_w  = i_immediate;
            o_inst_addr_w  = i_inst_addr;
            o_ALU_op_w     = i_ALU_op;
            o_write_flag_w = i_write_flag;
            o_valid_rs2_w  = i_valid_rs2;
            o_MemRead_w    = i_MemRead;
            o_MemWrite_w   = i_MemWrite;
            o_RegWrite_w   = i_RegWrite;
            o_ALU_src_w    = i_ALU_src;
            o_branch_w     = i_branch;
            o_finish_w     = i_finish;
        end
        else begin
            o_rs1_w        = 0;
            o_rs2_w        = 0;
            o_rd_w         = 0;
            o_read_data1_w = 0;
            o_read_data2_w = 0;
            o_immediate_w  = 0;
            o_inst_addr_w  = 0;
            o_ALU_op_w     = 0;
            o_write_flag_w = 0;
            o_valid_rs2_w  = 0;
            o_MemRead_w    = 0;
            o_MemWrite_w   = 0;
            o_RegWrite_w   = 0;
            o_ALU_src_w    = 0;
            o_branch_w     = 0;
            o_finish_w     = 0;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            o_rs1_r        <= 0;
            o_rs2_r        <= 0;
            o_rd_r         <= 0;
            o_read_data1_r <= 0;
            o_read_data2_r <= 0;
            o_immediate_r  <= 0;
            o_inst_addr_r  <= 0;
            o_ALU_op_r     <= 0;
            o_write_flag_r <= 0;
            o_valid_rs2_r  <= 0;
            o_MemRead_r    <= 0;
            o_MemWrite_r   <= 0;
            o_RegWrite_r   <= 0;
            o_ALU_src_r    <= 0;
            o_branch_r     <= 0;
            o_finish_r     <= 0;
        end
        else begin
            o_rs1_r        <= o_rs1_w;
            o_rs2_r        <= o_rs2_w;
            o_rd_r         <= o_rd_w;
            o_read_data1_r <= o_read_data1_w;
            o_read_data2_r <= o_read_data2_w;
            o_immediate_r  <= o_immediate_w;
            o_inst_addr_r  <= o_inst_addr_w;
            o_ALU_op_r     <= o_ALU_op_w;
            o_write_flag_r <= o_write_flag_w;
            o_valid_rs2_r  <= o_valid_rs2_w;
            o_MemRead_r    <= o_MemRead_w;
            o_MemWrite_r   <= o_MemWrite_w;
            o_RegWrite_r   <= o_RegWrite_w;
            o_ALU_src_r    <= o_ALU_src_w;
            o_branch_r     <= o_branch_w;
            o_finish_r     <= o_finish_w;        
        end
    end
endmodule

module MEM_pipeline(
    input                clk,
    input                rst_n,
    input          [4:0] i_rd,
    input  [`DATA_W-1:0] i_ALU_result,
    input  [`DATA_W-1:0] i_store_data,
    input                i_MemRead,
    input                i_MemWrite,
    input                i_RegWrite,
    input                i_finish,
    output         [4:0] o_rd,
    output [`DATA_W-1:0] o_ALU_result,
    output [`DATA_W-1:0] o_store_data,
    output               o_MemRead,
    output               o_MemWrite,
    output               o_RegWrite,
    output               o_finish
);
    reg         [4:0] o_rd_r, o_rd_w;
    reg [`DATA_W-1:0] o_ALU_result_r, o_ALU_result_w;
    reg [`DATA_W-1:0] o_store_data_r, o_store_data_w;
    reg               o_MemRead_r, o_MemRead_w;
    reg               o_MemWrite_r, o_MemWrite_w;
    reg               o_RegWrite_r, o_RegWrite_w;
    reg               o_finish_r, o_finish_w; 

    assign o_rd         = o_rd_r;
    assign o_ALU_result = o_ALU_result_r;
    assign o_store_data = o_store_data_r;
    assign o_MemRead    = o_MemRead_r;
    assign o_MemWrite   = o_MemWrite_r;
    assign o_RegWrite   = o_RegWrite_r;
    assign o_finish     = o_finish_r;

    always @(*) begin
            o_rd_w         = i_rd;
            o_ALU_result_w = i_ALU_result;
            o_store_data_w = i_store_data;
            o_MemRead_w    = i_MemRead;
            o_MemWrite_w   = i_MemWrite;
            o_RegWrite_w   = i_RegWrite;
            o_finish_w     = i_finish;
    end
    
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            o_rd_r         <= 0;
            o_ALU_result_r <= 0;
            o_store_data_r <= 0;
            o_MemRead_r    <= 0;
            o_MemWrite_r   <= 0;
            o_RegWrite_r   <= 0;
            o_finish_r     <= 0;
        end
        else begin
            o_rd_r         <= o_rd_w;
            o_ALU_result_r <= o_ALU_result_w;
            o_store_data_r <= o_store_data_w;
            o_MemRead_r    <= o_MemRead_w;
            o_MemWrite_r   <= o_MemWrite_w;
            o_RegWrite_r   <= o_RegWrite_w;
            o_finish_r     <= o_finish_w;
        end
    end
endmodule

module WB_pipeline(
    input                clk,
    input                rst_n,
    input          [4:0] i_rd,
    input  [`DATA_W-1:0] i_ALU_result,
    input  [`DATA_W-1:0] i_MEM_result,
    input                i_MemRead,
    input                i_RegWrite,
    input                i_finish,
    output         [4:0] o_rd,
    output [`DATA_W-1:0] o_ALU_result,
    output [`DATA_W-1:0] o_MEM_result,
    output               o_MemRead,
    output               o_RegWrite,
    output               o_finish
);
    reg         [4:0] o_rd_r, o_rd_w;
    reg [`DATA_W-1:0] o_ALU_result_r, o_ALU_result_w;
    reg [`DATA_W-1:0] o_MEM_result_r, o_MEM_result_w;
    reg               o_MemRead_r, o_MemRead_w;
    reg               o_RegWrite_r, o_RegWrite_w;
    reg               o_finish_r, o_finish_w;

    assign o_rd         = o_rd_r;
    assign o_ALU_result = o_ALU_result_r;
    assign o_MEM_result = o_MEM_result_r;
    assign o_MemRead    = o_MemRead_r;
    assign o_RegWrite   = o_RegWrite_r;
    assign o_finish     = o_finish_r;

    always @(*) begin
            o_rd_w         = i_rd;
            o_ALU_result_w = i_ALU_result;
            o_MEM_result_w = i_MEM_result;
            o_MemRead_w    = i_MemRead;
            o_RegWrite_w   = i_RegWrite;
            o_finish_w     = i_finish;
    end
    
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            o_rd_r         <= 0;
            o_ALU_result_r <= 0;
            o_MEM_result_r <= 0;
            o_MemRead_r    <= 0;
            o_RegWrite_r   <= 0;
            o_finish_r     <= 0;
        end
        else begin
            o_rd_r         <= o_rd_w;
            o_ALU_result_r <= o_ALU_result_w;
            o_MEM_result_r <= o_MEM_result_w;
            o_MemRead_r    <= o_MemRead_w;
            o_RegWrite_r   <= o_RegWrite_w;
            o_finish_r     <= o_finish_w;
        end
    end
endmodule

module MUX_PC(
    input  [7:0] i0,
    input  [7:0] i1,
    input        sel,
    output [7:0] o0
);
    assign o0 = (sel)? i1: i0;
endmodule

module MUX_2_1(
    input [`DATA_W-1:0] i0,
    input [`DATA_W-1:0] i1,
    input               sel,
    output [`DATA_W-1:0] o0
);
    assign o0 = (sel)? i1: i0;
endmodule

module MUX_4_1(
    input [`DATA_W-1:0] i0,
    input [`DATA_W-1:0] i1,
    input [`DATA_W-1:0] i2,
    input [`DATA_W-1:0] i3,
    input         [1:0] sel,
    output [`DATA_W-1:0] o0
);
    assign o0 = (sel==2'b00)? i0: (sel==2'b01)? i1: (sel==2'b10)? i2: i3;
endmodule

module ALU_control(
    input [6:0] opcode,
    input [2:0] funct3,
    input [6:0] funct7,
    output [2:0] ALU_op
);
    assign ALU_op = (opcode == 7'b0000011 || opcode == 7'b0100011)? 3'b001:
                    (opcode == 7'b0010011)? (
                        (funct3 == 3'b000)? 3'b001:
                        (funct3 == 3'b100)? 3'b011:
                        (funct3 == 3'b110)? 3'b100:
                        (funct3 == 3'b111)? 3'b101:
                        (funct3 == 3'b001)? 3'b110:
                        (funct3 == 3'b101)? 3'b111: 0):
                    (opcode == 7'b0110011)? (
                        (funct3 == 3'b000)? ((funct7[5])? 3'b010: 3'b001): 
                        (funct3 == 3'b100)? 3'b011:
                        (funct3 == 3'b110)? 3'b100:
                        (funct3 == 3'b111)? 3'b101: 0): 0;
endmodule

module ALU(
    input                clk,
    input                rst_n,
    input  [`DATA_W-1:0] input1,
    input  [`DATA_W-1:0] input2,
    input          [2:0] ALU_op,
    output [`DATA_W-1:0] result
);
    wire [`DATA_W-1:0] add_res, sub_res;

    reg [`DATA_W-1:0] temp_input1, temp_input2;

    Adder64 add(.iA(temp_input1), .iB(temp_input2), .iC(1'b0), .oS(add_res), .oP(), .oG(), .oC());
    Adder64 sub(.iA(temp_input1), .iB(~temp_input2), .iC(1'b1), .oS(sub_res), .oP(), .oG(), .oC());

    assign result = (ALU_op == 3'b001)? add_res:
                    (ALU_op == 3'b010)? sub_res:
                    (ALU_op == 3'b011)? temp_input1 ^ temp_input2:
                    (ALU_op == 3'b100)? temp_input1 | temp_input2:
                    (ALU_op == 3'b101)? temp_input1 & temp_input2:
                    (ALU_op == 3'b110)? temp_input1 << temp_input2[7:0]:
                    (ALU_op == 3'b111)? temp_input1 >> temp_input2[7:0]: 0;

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            temp_input1 <= 0;
            temp_input2 <= 0;
        end
        else begin
            temp_input1 <= input1;
            temp_input2 <= input2;
        end
    end
endmodule

module CLA4(
    input  [3:0] iG,
    input  [3:0] iP,
    input  iC,
    output oG,
    output oP,
    output [4:0] oC
);
    assign oC[0] = iC;
    assign oC[1] = iG[0] | (iP[0] & oC[0]);
    assign oC[2] = iG[1] | (iP[1] & iG[0]) | (iP[1] & iP[0] & oC[0]);
    assign oC[3] = iG[2] | (iP[2] & iG[1]) | (iP[2] & iP[1] & iG[0]) | (iP[2] & iP[1] & iP[0] & oC[0]);

    assign oG = iG[3] | (iP[3] & iG[2]) | (iP[3] & iP[2] & iG[1]) | (iP[3] & iP[2] & iP[1] & iG[0]);
    assign oP = iP[3] & iP[2] & iP[1] & iP[0];

    assign oC[4] = oG | (oP & oC[0]);

endmodule

module Adder4(
    input  [3:0] iA,
    input  [3:0] iB,
    input  iC,
    output [3:0] oS,
    output oG,
    output oP,
    output oC
);
    wire [3:0] G = iA & iB;
    wire [3:0] P = iA | iB;
    wire [3:0] C;

    CLA4 cla(.iG(G), .iP(P), .iC(iC), .oG(oG), .oP(oP), .oC({oC, C}));

    assign oS = iA ^ iB ^ C;

endmodule

module Adder16(
    input  [15:0] iA,
    input  [15:0] iB,
    input  iC,
    output [15:0] oS,
    output oG,
    output oP,
    output oC
);
    wire [3:0] G;
    wire [3:0] P;
    wire [3:0] C;

    Adder4 adder0(.iA(iA[ 3: 0]), .iB(iB[ 3: 0]), .iC(C[0]), .oS(oS[ 3: 0]), .oG(G[0]), .oP(P[0]));
    Adder4 adder1(.iA(iA[ 7: 4]), .iB(iB[ 7: 4]), .iC(C[1]), .oS(oS[ 7: 4]), .oG(G[1]), .oP(P[1]));
    Adder4 adder2(.iA(iA[11: 8]), .iB(iB[11: 8]), .iC(C[2]), .oS(oS[11: 8]), .oG(G[2]), .oP(P[2]));
    Adder4 adder3(.iA(iA[15:12]), .iB(iB[15:12]), .iC(C[3]), .oS(oS[15:12]), .oG(G[3]), .oP(P[3]));

    CLA4 cla(.iG(G), .iP(P), .iC(iC), .oG(oG), .oP(oP), .oC({oC, C}));

endmodule

module Adder64(
    input  [63:0] iA,
    input  [63:0] iB,
    input  iC,
    output [63:0] oS,
    output oG,
    output oP,
    output oC
);
    wire [3:0] G;
    wire [3:0] P;
    wire [3:0] C;

    Adder16 adder0(.iA(iA[15: 0]), .iB(iB[15: 0]), .iC(C[0]), .oS(oS[15: 0]), .oG(G[0]), .oP(P[0]));
    Adder16 adder1(.iA(iA[31:16]), .iB(iB[31:16]), .iC(C[1]), .oS(oS[31:16]), .oG(G[1]), .oP(P[1]));
    Adder16 adder2(.iA(iA[47:32]), .iB(iB[47:32]), .iC(C[2]), .oS(oS[47:32]), .oG(G[2]), .oP(P[2]));
    Adder16 adder3(.iA(iA[63:48]), .iB(iB[63:48]), .iC(C[3]), .oS(oS[63:48]), .oG(G[3]), .oP(P[3]));

    CLA4 cla(.iG(G), .iP(P), .iC(iC), .oG(oG), .oP(oP), .oC({oC, C}));

endmodule