module data_memory #(
    parameter ADDR_W = 64,
    parameter DATA_W = 64
)(
    input               i_clk,
    input               i_rst_n,
    input  [DATA_W-1:0] i_data,
    input  [ADDR_W-1:0] i_r_addr,
    input  [ADDR_W-1:0] i_w_addr,
    input               i_MemRead,
    input               i_MemWrite,
    output              o_valid,
    output [DATA_W-1:0] o_data
);
    integer i;
    reg [7:0] mem   [0:1023];

    always @(*) begin
        if (i_MemWrite) begin
            mem[i_w_addr+0] = i_data[ 7:0] ;
            mem[i_w_addr+1] = i_data[15:8] ;
            mem[i_w_addr+2] = i_data[23:16];
            mem[i_w_addr+3] = i_data[31:24];
            mem[i_w_addr+4] = i_data[39:32];
            mem[i_w_addr+5] = i_data[47:40];  
            mem[i_w_addr+6] = i_data[55:48];
            mem[i_w_addr+7] = i_data[63:56];
        end
    end

    assign o_valid = (i_MemRead || i_MemWrite);
    assign o_data = (i_MemRead) ? {mem[i_r_addr+7], mem[i_r_addr+6],
                                         mem[i_r_addr+5], mem[i_r_addr+4],
                                         mem[i_r_addr+3], mem[i_r_addr+2], 
                                         mem[i_r_addr+1], mem[i_r_addr+0]} : 0;


    always @(negedge i_rst_n) begin
        for (i = 0; i < 1024; i = i + 1) mem[i] <= 0;
    end

/*
    reg              o_valid_r, o_valid_w;
    reg [DATA_W-1:0] o_data_r,  o_data_w;
    
    integer i;
    
    assign o_valid = o_valid_r;
    assign o_data  = o_data_r;
    always @(*) begin
        if (i_MemWrite) begin
            mem[i_w_addr+0] = i_data[ 7:0] ;
            mem[i_w_addr+1] = i_data[15:8] ;
            mem[i_w_addr+2] = i_data[23:16];
            mem[i_w_addr+3] = i_data[31:24];
            mem[i_w_addr+4] = i_data[39:32];
            mem[i_w_addr+5] = i_data[47:40];  
            mem[i_w_addr+6] = i_data[55:48];
            mem[i_w_addr+7] = i_data[63:56];
        end 
        o_valid_w = (i_MemRead) ? 1 : 0;
        o_data_w  = (i_MemRead) ? {mem[i_r_addr+7], mem[i_r_addr+6],
                                         mem[i_r_addr+5], mem[i_r_addr+4],
                                         mem[i_r_addr+3], mem[i_r_addr+2], 
                                         mem[i_r_addr+1], mem[i_r_addr+0]} : 0;
    end
    always @(posedge i_clk or negedge i_rst_n) begin
        if (~i_rst_n) begin
            o_valid_r        <= 0;
            o_data_r         <= 0;
            for (i=0; i<1024; i = i + 1)
                mem[i] <= 0;
        end else begin
            o_valid_r        <= o_valid_w;
            o_data_r         <= o_data_w;
        end
    end
*/
endmodule 
